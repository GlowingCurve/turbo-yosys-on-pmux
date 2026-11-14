#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "pmux_common.h"
#include "pmux_rewrite.h"

#include <algorithm>
#include <array>
#include <map>
#include <memory>
#include <ranges>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ArithmeticExpression
{
	std::map<SigSpec, int> terms;
	Const offset;
	bool has_offset = false;
	bool simplified = false;

	explicit ArithmeticExpression(int width) : offset(0, width) {}
};

struct ArithmeticColumn
{
	SigSpec operand;
	std::vector<SigSpec> variants;
	std::vector<std::pair<int, int>> varying_bits;
	bool subtract;
};

using ArithmeticPlan = std::vector<ArithmeticColumn>;

bool arithmetic_type(IdString type)
{
	return type.in(ID($add), ID($sub), ID($neg));
}

SigSpec trim_zero_extension(const SigSpec &value)
{
	int width = GetSize(value);
	while (width > 1 && value[width - 1] == State::S0)
		width--;
	return value.extract(0, width);
}

std::vector<SigSpec> arithmetic_arms(PmuxCoarseIndex &index, Cell *cell, int width, int count)
{
	auto data = index.port(cell, ID::B);
	int branch_width = GetSize(cell->getPort(ID::Y));
	std::vector<SigSpec> arms{index.port(cell, ID::A)};
	log_assert(GetSize(arms.front()) == branch_width && int64_t{branch_width} * count == GetSize(data));
	arms.front() = arms.front().extract(0, width);
	for (int i = 0; i < count; i++)
		arms.push_back(data.extract(i * branch_width, width));
	return arms;
}

struct ArithmeticRewrite
{
	PmuxCoarseIndex &index;
	int width;
	bool external_inputs, has_selector;
	int remaining = 2048;
	int binary_remaining = 65536;
	pool<Cell *> region;
	pool<Cell *> binary_cells, active;

	ArithmeticRewrite(PmuxCoarseIndex &index, int width, bool external_inputs, bool has_selector)
			: index(index), width(width), external_inputs(external_inputs), has_selector(has_selector) {}

	bool binary(const SigSpec &value, int depth = 0)
	{
		if (depth > 128 || (binary_remaining -= GetSize(value)) < 0)
			return false;
		for (SigBit bit : value) {
			if (!bit.wire) {
				if (bit != State::S0 && bit != State::S1)
					return false;
				continue;
			}
			auto cell = index.driver(bit);
			if (!cell && (!external_inputs || !index.module_input(bit)))
				return false;
			if (!cell || binary_cells.count(cell))
				continue;
			if (!cell->type.in(ID($add), ID($sub), ID($neg), ID($mul), ID($not), ID($and), ID($or), ID($xor), ID($xnor),
					ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and), ID($logic_or),
					ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor),
					ID($mux), ID($slice), ID($concat)) || !active.insert(cell).second)
				return false;
			for (const auto &[name, input] : cell->connections())
				if (cell->input(name) && !binary(index.sigmap(input), depth + 1)) {
					active.erase(cell);
					return false;
				}
			active.erase(cell);
			binary_cells.insert(cell);
		}
		return true;
	}

	bool expand(SigSpec value, int sign, ArithmeticExpression &expression, int depth = 0)
	{
		if (--remaining < 0 || depth > 12 || GetSize(expression.terms) > 16)
			return false;
		if (value.is_fully_const()) {
			if (!value.is_fully_def())
				return false;
			expression.simplified |= expression.has_offset || value.is_fully_zero();
			expression.has_offset = true;
			expression.offset = sign > 0 ? const_add(expression.offset, value.as_const(), false, false, width)
				: const_sub(expression.offset, value.as_const(), false, false, width);
			return true;
		}

		Cell *driver = index.driver(value[0]);
		if (driver && arithmetic_type(driver->type) && index.editable(driver)) {
			SigSpec a = index.port(driver, ID::A);
			bool unary = driver->type == ID($neg);
			auto b = unary ? SigSpec() : index.port(driver, ID::B);
			bool is_signed = pmux_is_signed_port(driver, ID::A) && (unary || pmux_is_signed_port(driver, ID::B));
			SigSpec output = index.port(driver, ID::Y);
			const int output_width = GetSize(output);
			const int compared_width = std::min(output_width, width);
			bool matches = output.extract(0, compared_width) == value.extract(0, compared_width);
			if (output_width < width) {
				// A narrowed result can be widened only when the original operation cannot overflow.
				matches &= (is_signed || driver->type == ID($add)) && output_width > std::max(GetSize(a), GetSize(b));
				output.extend_u0(width, is_signed);
				matches &= output == value;
			}
			if (matches) {
				// A widened branch can retain known bits even when the operation yields X.
				if (has_selector && depth == 0 && output_width < width && !binary(value))
					return false;
				region.insert(driver);
				a.extend_u0(width, is_signed);
				if (unary)
					return expand(a, -sign, expression, depth + 1);
				b.extend_u0(width, is_signed);
				return expand(a, sign, expression, depth + 1) &&
					expand(b, driver->type == ID($sub) ? -sign : sign, expression, depth + 1);
			}
		}

		if (has_selector && depth == 0 && !binary(value))
			return false;
		for (SigBit bit : value)
			if (!bit.wire && bit != State::S0 && bit != State::S1)
				return false;
		value = trim_zero_extension(value);
		int &coefficient = expression.terms[value];
		expression.simplified |= coefficient != 0 && (coefficient > 0) != (sign > 0);
		coefficient += sign;
		if (coefficient == 0)
			expression.terms.erase(value);
		return true;
	}
};

void add_column(ArithmeticPlan &plan, std::vector<SigSpec> values, const std::vector<bool> &defined, bool subtract)
{
	int width = 0;
	for (int i = 0; i < GetSize(values); i++)
		if (defined[i])
			width = std::max(width, GetSize(values[i]));

	for (auto &value : values)
		value.extend_u0(width);
	int first = std::find(defined.begin(), defined.end(), true) - defined.begin();
	log_assert(first < GetSize(values));
	ArithmeticColumn column{values[first], {}, {}, subtract};
	dict<SigSpec, int> lanes;
	for (int bit = 0; bit < width; bit++) {
		SigSpec lane;
		bool common = true;
		for (int branch = 0; branch < GetSize(values); branch++) {
			auto value = values[branch][bit];
			common &= !defined[branch] || value == column.operand[bit];
			lane.append(defined[branch] ? value : SigBit(State::Sx));
		}
		if (common)
			continue;

		auto [slot, inserted] = lanes.emplace(lane, GetSize(lanes));
		column.varying_bits.emplace_back(bit, slot->second);
		column.operand[bit] = State::S0;
		if (inserted) {
			if (column.variants.empty())
				column.variants.resize(GetSize(values));
			for (int branch = 0; branch < GetSize(values); branch++)
				column.variants[branch].append(lane[branch]);
		}
	}

	if (!column.variants.empty() || !column.operand.is_fully_zero())
		plan.push_back(std::move(column));
}

ArithmeticPlan make_term_columns(const std::vector<std::vector<SigSpec>> &terms, const std::vector<bool> &defined,
		int count, bool subtract)
{
	ArithmeticPlan plan;
	for (int column = 0; column < count; column++) {
		std::vector<SigSpec> values;
		for (const auto &branch : terms)
			values.push_back(column < GetSize(branch) ? branch[column] : SigSpec(State::S0));
		add_column(plan, std::move(values), defined, subtract);
	}
	return plan;
}

std::pair<int, int> selected_width(const ArithmeticPlan &plan)
{
	int bits = 0, cells = 0;
	for (const auto &column : plan)
		if (!column.variants.empty()) {
			bits += GetSize(column.variants.front());
			cells++;
		}
	return {bits, cells};
}

void improve_term_columns(ArithmeticPlan &best, std::vector<std::vector<SigSpec>> &terms,
		const std::vector<bool> &defined, int columns)
{
	std::vector<int> branches;
	int width = 0;
	for (int i = 0; i < GetSize(terms); i++) {
		if (!defined[i])
			continue;
		if (GetSize(terms[i]) != columns || GetSize(branches) == 4)
			return;
		branches.push_back(i);
		for (const auto &term : terms[i])
			width = std::max(width, GetSize(term));
	}
	if (GetSize(branches) < 2)
		return;
	int combinations = 1;
	for (int i = 1; i < GetSize(branches); i++)
		for (int permutation = 2; permutation <= columns; permutation++)
			combinations *= permutation;
	constexpr int permutation_work_limit = 1 << 18;
	if (int64_t{columns} * combinations * width * GetSize(terms) > permutation_work_limit)
		return;

	auto best_width = selected_width(best);
	// Permuting all columns together leaves the selector cost unchanged.
	auto enumerate = [&](auto &self, int branch) -> void {
		if (branch == GetSize(branches)) {
			auto candidate = make_term_columns(terms, defined, columns, false);
			auto width = selected_width(candidate);
			if (width < best_width) {
				best = std::move(candidate);
				best_width = width;
			}
			return;
		}
		auto &row = terms[branches[branch]];
		do {
			self(self, branch + 1);
		} while (std::next_permutation(row.begin(), row.end()));
	};
	enumerate(enumerate, 1);
}

ArithmeticPlan make_column_plan(std::vector<ArithmeticExpression> expressions, const std::vector<bool> &defined)
{
	ArithmeticPlan plan;
	int first = std::find(defined.begin(), defined.end(), true) - defined.begin();
	for (int sign : {1, -1}) {
		// Emit common terms before allocating selector inputs to the remaining terms.
		for (auto [term, coefficient] : expressions[first].terms) {
			int common = coefficient * sign;
			for (int i = 0; i < GetSize(expressions) && common > 0; i++) {
				if (!defined[i])
					continue;
				auto entry = expressions[i].terms.find(term);
				common = entry == expressions[i].terms.end() ? 0 : std::min(common, entry->second * sign);
			}
			for (int n = 0; n < common; n++)
				plan.push_back({term, {}, {}, sign < 0});
			if (common > 0)
				for (int i = 0; i < GetSize(expressions); i++)
					if (defined[i])
						expressions[i].terms.at(term) -= common * sign;
		}

		std::vector<std::vector<SigSpec>> terms(GetSize(expressions));
		int count = 0;
		for (int i = 0; i < GetSize(expressions); i++) {
			for (auto &[term, coefficient] : expressions[i].terms)
				for (int n = 0; n < coefficient * sign; n++)
					terms[i].push_back(term);
			count = std::max(count, GetSize(terms[i]));
		}
		auto columns = make_term_columns(terms, defined, count, sign < 0);
		if (sign > 0 && count == 3)
			improve_term_columns(columns, terms, defined, count);
		std::ranges::move(columns, std::back_inserter(plan));
	}

	return plan;
}

ArithmeticPlan make_exclusion_plan(const std::vector<ArithmeticExpression> &expressions, const std::vector<bool> &defined,
		ArithmeticRewrite &rewrite)
{
	std::set<SigSpec> total;
	for (const auto &expression : expressions)
		for (const auto &[term, coefficient] : expression.terms) {
			if (coefficient != 1)
				return {};
			total.insert(term);
		}
	if (GetSize(total) < 3)
		return {};
	// The total includes terms unused by individual branches. They must be binary
	// so an unknown term cannot contaminate a branch that originally omitted it.
	for (const auto &term : total)
		if (!rewrite.binary(term))
			return {};

	std::vector<SigSpec> excluded(GetSize(expressions), State::S0);
	for (int i = 0; i < GetSize(expressions); i++) {
		if (!defined[i])
			continue;
		if (GetSize(expressions[i].terms) != GetSize(total) - 1)
			return {};
		for (const auto &term : total)
			if (!expressions[i].terms.count(term)) {
				excluded[i] = term;
				break;
			}
	}

	ArithmeticPlan plan;
	for (const auto &term : total)
		plan.push_back({term, {}, {}, false});
	add_column(plan, std::move(excluded), defined, true);
	return plan;
}

struct ExtremumPredicates
{
	enum Row { less, equal, greater, unknown_different, unknown, row_count };
	using Values = std::array<State, row_count>;

	PmuxCoarseIndex &index;
	SigSpec lhs, rhs;
	bool signed_order;
	std::vector<std::pair<Row, SigBit>> strict_selects;
	pool<Cell *> region;
	dict<SigBit, Values> evaluated;
	std::array<bool, 3> seen{};
	int remaining = 512;

	static bool strict_comparison(Cell *cell) { return cell->type.in(ID($lt), ID($gt)); }

	static bool predicate_gate(Cell *cell)
	{
		return cell->type.in(ID($eq), ID($ne), ID($not), ID($logic_not), ID($and), ID($or), ID($xor), ID($xnor),
				ID($logic_and), ID($logic_or), ID($reduce_bool), ID($reduce_or), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor));
	}

	static Cell *find_order(PmuxCoarseIndex &index, const SigSpec &select)
	{
		std::vector<std::pair<SigBit, int>> pending;
		pool<SigBit> visited;
		auto enqueue = [&](const SigSpec &inputs, int depth) {
			for (auto bit : inputs) {
				if (GetSize(pending) == 256)
					break;
				if (bit.wire && visited.insert(bit).second)
					pending.emplace_back(bit, depth);
			}
		};
		enqueue(select, 0);
		for (int i = 0; i < GetSize(pending); ++i) {
			auto [bit, depth] = pending[i];
			auto source = index.source(bit);
			if (!source || source->port != ID::Y || GetSize(source->cell->getPort(ID::Y)) != 1)
				continue;
			auto cell = source->cell;
			if (strict_comparison(cell))
				return cell;
			if (depth < 12 && predicate_gate(cell))
				for (auto port : {ID::A, ID::B})
					if (cell->hasPort(port) && GetSize(cell->getPort(port)) <= 64)
						enqueue(index.port(cell, port), depth + 1);
		}
		return nullptr;
	}

	static bool signed_comparison(Cell *cell)
	{
		return pmux_is_signed_port(cell, ID::A) && pmux_is_signed_port(cell, ID::B);
	}

	ExtremumPredicates(PmuxCoarseIndex &index, Cell *order) : index(index), lhs(index.port(order, ID::A)),
			rhs(index.port(order, ID::B)), signed_order(signed_comparison(order))
	{
		int width = std::max(GetSize(lhs), GetSize(rhs));
		lhs.extend_u0(width, signed_order);
		rhs.extend_u0(width, signed_order);
	}

	std::optional<Row> relation(Cell *cell)
	{
		bool is_equal = cell->type == ID($eq);
		bool is_signed = signed_comparison(cell);
		if (!is_equal && is_signed != signed_order)
			return std::nullopt;
		auto a = index.port(cell, ID::A), b = index.port(cell, ID::B);
		int width = std::max(GetSize(a), GetSize(b));
		if (a.empty() || b.empty() || width > 4096)
			return std::nullopt;
		a.extend_u0(width, is_signed);
		b.extend_u0(width, is_signed);
		// Extend the equal-width operands together for the equality check.
		width = std::max(width, GetSize(lhs));
		a.extend_u0(width, signed_order);
		b.extend_u0(width, signed_order);
		auto left = lhs, right = rhs;
		left.extend_u0(width, signed_order);
		right.extend_u0(width, signed_order);
		bool swapped = a == right && b == left;
		if (!swapped && (a != left || b != right))
			return std::nullopt;
		if (is_equal)
			return equal;
		return (cell->type == ID($lt)) != swapped ? less : greater;
	}

	std::optional<Values> evaluate(SigBit bit, int depth = 0)
	{
		if (depth > 12 || --remaining < 0)
			return std::nullopt;
		if (!bit.wire) {
			if (bit != State::S0 && bit != State::S1)
				return std::nullopt;
			Values values;
			values.fill(bit.data);
			return values;
		}
		auto cached = evaluated.find(bit);
		if (cached != evaluated.end())
			return cached->second;
		auto source = index.source(bit);
		if (!source || source->port != ID::Y || GetSize(source->cell->getPort(ID::Y)) != 1)
			return std::nullopt;
		auto cell = source->cell;
		Values values;
		auto ordering = strict_comparison(cell) || cell->type == ID($eq) ? relation(cell) : std::nullopt;
		if (ordering) {
			values = {State::S0, State::S0, State::S0, State::Sx, State::Sx};
			values[*ordering] = State::S1;
			if (*ordering == equal)
				values[unknown_different] = State::S0;
			else
				strict_selects.emplace_back(*ordering, bit);
			seen[*ordering] = true;
		} else {
			if (!predicate_gate(cell))
				return std::nullopt;
			std::array<Const, row_count> a, b;
			for (auto port : {ID::A, ID::B}) {
				if (!cell->hasPort(port))
					continue;
				auto &operand = port == ID::A ? a : b;
				for (auto input : index.port(cell, port)) {
					auto input_values = evaluate(input, depth + 1);
					if (!input_values)
						return std::nullopt;
					for (int row = 0; row < row_count; ++row)
						operand[row].append((*input_values)[row]);
				}
			}
			for (int row = 0; row < row_count; ++row)
				values[row] = CellTypes::eval(cell, a[row], b[row])[0];
		}
		region.insert(cell);
		evaluated.emplace(bit, values);
		return values;
	}
};

bool match_equal_arm(PmuxCoarseIndex &index, const SigSpec &value, const SigSpec &lhs, const SigSpec &rhs, pool<Cell *> &region)
{
	if (value == lhs || value == rhs)
		return true;
	auto cell = index.driver(value[0]);
	if (!cell || !cell->type.in(ID($and), ID($or)))
		return false;
	int width = GetSize(value);
	auto output = index.port(cell, ID::Y);
	auto a = index.port(cell, ID::A), b = index.port(cell, ID::B);
	bool is_signed = ExtremumPredicates::signed_comparison(cell);
	int result_width = std::min(GetSize(output), width);
	for (int offset = 0; offset < result_width; ++offset) {
		auto source = index.source(output[offset]);
		if (!source || source->cell != cell || source->port != ID::Y || source->offset != offset)
			return false;
	}
	a.extend_u0(result_width, is_signed);
	b.extend_u0(result_width, is_signed);
	for (bool sign_extend : {false, true}) {
		auto padded = [&](SigSpec signal) {
			signal.extend_u0(width, sign_extend);
			return signal;
		};
		if (padded(output) != value)
			continue;
		auto left = padded(a), right = padded(b);
		if ((left == lhs || left == rhs) && (right == lhs || right == rhs)) {
			region.insert(cell);
			return true;
		}
	}
	return false;
}

bool rewrite_extremum(PmuxCoarseIndex &index, Cell *root)
{
	if (!index.editable(root))
		return false;
	auto select = index.port(root, ID::S);
	int width = GetSize(root->getPort(ID::Y));
	if (width > 4096 || select.empty() || GetSize(select) > 16)
		return false;

	Cell *order = ExtremumPredicates::find_order(index, select);
	if (!order || order->getPort(ID::A).empty() || order->getPort(ID::B).empty() ||
			std::max(GetSize(order->getPort(ID::A)), GetSize(order->getPort(ID::B))) > 4096)
		return false;
	ExtremumPredicates predicates(index, order);
	if (predicates.lhs == predicates.rhs)
		return false;
	for (const auto *operand : {&predicates.lhs, &predicates.rhs})
		for (auto bit : *operand)
			if (!bit.wire && bit != State::S0 && bit != State::S1)
				return false;
	std::array<SigSpec, ExtremumPredicates::row_count> choices;
	for (auto bit : select) {
		auto values = predicates.evaluate(bit);
		if (!values)
			return false;
		for (int row = 0; row < ExtremumPredicates::row_count; ++row)
			choices[row].append((*values)[row]);
	}
	if (std::find(predicates.seen.begin(), predicates.seen.end(), false) != predicates.seen.end())
		return false;

	auto arms = arithmetic_arms(index, root, width, GetSize(select));
	std::array<SigSpec, 3> selected;
	for (int row = 0; row < ExtremumPredicates::row_count; ++row) {
		auto choice = choices[row].as_const();
		bool binary_row = row < ExtremumPredicates::unknown_different;
		int branch = 0;
		if (!choice.is_fully_zero()) {
			if (!choice.is_onehot(&branch)) {
				if (binary_row)
					return false;
				continue;
			}
			branch++;
		}
		const auto &arm = arms.at(branch);
		if (binary_row)
			selected[row] = arm;
		// An unknown comparison can be refined only when the original result is entirely X.
		else if (!arm.is_fully_const() || !arm.as_const().is_fully_undef_x_only())
			return false;
	}

	for (bool sign_extend : {true, false}) {
		if (sign_extend && !predicates.signed_order)
			continue;
		auto lhs = predicates.lhs, rhs = predicates.rhs;
		lhs.extend_u0(width, sign_extend);
		rhs.extend_u0(width, sign_extend);
		bool minimum = selected[ExtremumPredicates::less] == lhs && selected[ExtremumPredicates::greater] == rhs;
		bool maximum = selected[ExtremumPredicates::less] == rhs && selected[ExtremumPredicates::greater] == lhs;
		if (!minimum && !maximum)
			continue;
		auto region = predicates.region;
		if (!match_equal_arm(index, selected[ExtremumPredicates::equal], lhs, rhs, region))
			continue;
		region.insert(root);
		std::unique_ptr<PmuxRewrite> best;
		bool best_uses_less = false;
		for (auto [relation, control] : predicates.strict_selects) {
			bool uses_less = relation == ExtremumPredicates::less;
			bool select_lhs = minimum == uses_less;
			auto candidate = std::make_unique<PmuxRewrite>(index.module, index, "arith_extremum");
			auto result = pmux_emit_mux(&candidate->staging, control, select_lhs ? rhs : lhs, select_lhs ? lhs : rhs,
					root->get_src_attribute());
			candidate->connect(root->getPort(ID::Y), result);
			candidate->find_removable(region);
			if (!candidate->removed.count(root))
				continue;
			if (best && std::make_pair(GetSize(candidate->removed), uses_less) <= std::make_pair(GetSize(best->removed), best_uses_less))
				continue;
			if (!candidate->validate())
				continue;
			best = std::move(candidate);
			best_uses_less = uses_less;
		}
		if (!best)
			continue;
		log("  Rewriting extremum at %s.%s (%d cells removed, %d added).\n",
				log_id(index.module), log_id(root), GetSize(best->removed), best->added_count());
		best->commit();
		return true;
	}
	return false;
}

SigSpec emit_arithmetic(Module *module, const ArithmeticPlan &plan, const SigSpec &select, int width)
{
	SigSpec result(State::S0);
	bool has_result = false;
	for (bool subtract : {false, true}) {
		for (const auto &column : plan) {
			if (column.subtract != subtract)
				continue;
			SigSpec operand = column.operand;
			if (!column.variants.empty()) {
				SigSpec cases;
				for (int i = 1; i < GetSize(column.variants); i++)
					cases.append(column.variants[i]);
				SigSpec selected = GetSize(select) == 1
					? pmux_emit_mux(module, select, column.variants.front(), cases)
					: module->Pmux(NEW_ID, column.variants.front(), cases, select);
				for (auto [bit, slot] : column.varying_bits)
					operand[bit] = selected[slot];
			}
			if (has_result || subtract) {
				SigSpec sum(module->addWire(NEW_ID, width));
				if (subtract)
					module->addSub(NEW_ID, result, operand, sum);
				else
					module->addAdd(NEW_ID, result, operand, sum);
				result = sum;
			} else {
				result = operand;
			}
			has_result = true;
		}
	}
	result.extend_u0(width);
	return result;
}

enum class ArithmeticTransform { ExcludedTerm, CommonColumns };

bool rewrite_arithmetic(PmuxCoarseIndex &index, Cell *root, bool external_inputs, ArithmeticTransform transform)
{
	bool has_selector = root->type.in(ID($mux), ID($pmux));
	log_assert(has_selector || arithmetic_type(root->type));
	log_assert(transform != ArithmeticTransform::ExcludedTerm || (has_selector && GetSize(root->getPort(ID::S)) >= 2));
	if (!index.editable(root))
		return false;
	SigSpec output = index.port(root, ID::Y);
	int width = GetSize(output);
	ArithmeticRewrite rewrite{index, width, external_inputs, has_selector};
	SigSpec select;
	std::vector<SigSpec> branches;
	if (!has_selector) {
		branches.push_back(output);
	} else {
		select = index.port(root, ID::S);
		int count = GetSize(select);
		if (count == 0 || count > pmux_max_rows)
			return false;
		branches = arithmetic_arms(index, root, width, count);
		if (std::none_of(branches.begin(), branches.end(), [&](const SigSpec &branch) {
			Cell *driver = branch.empty() ? nullptr : index.driver(branch[0]);
			return driver && arithmetic_type(driver->type);
		}))
			return false;
		// A binary mux merges its branches bit by bit for an unknown selector.
		// Selecting an arithmetic operand before its operation may lose known bits.
		if (root->type == ID($mux) && !rewrite.binary(select))
			return false;
	}

	std::vector<ArithmeticExpression> expressions;
	std::vector<bool> defined;
	for (const SigSpec &branch : branches) {
		expressions.emplace_back(width);
		bool unspecified = branch.is_fully_const() && branch.as_const().is_fully_undef_x_only();
		defined.push_back(!unspecified);
		if (unspecified)
			continue;
		if (!rewrite.expand(branch, 1, expressions.back()))
			return false;
	}
	if (rewrite.region.empty())
		return false;
	if (!has_selector && !expressions.front().simplified && !expressions.front().terms.empty())
		return false;
	rewrite.region.insert(root);

	bool exclusion = transform == ArithmeticTransform::ExcludedTerm;
	auto plan = exclusion ? make_exclusion_plan(expressions, defined, rewrite) : make_column_plan(expressions, defined);
	if (exclusion && plan.empty())
		return false;
	std::vector<SigSpec> offsets;
	for (const auto &expression : expressions)
		offsets.push_back(trim_zero_extension(expression.offset));
	add_column(plan, std::move(offsets), defined, false);

	PmuxRewrite candidate(index.module, index, exclusion ? "arith_excluded_term" : "arith_common_columns");
	auto result = emit_arithmetic(&candidate.staging, plan, select, width);
	candidate.connect(root->getPort(ID::Y), result);
	candidate.find_removable(rewrite.region);
	if (!candidate.removed.count(root) || candidate.added_count() >= GetSize(candidate.removed) || !candidate.validate())
		return false;
	log("  Rewriting arithmetic at %s.%s (%d cells removed, %d added).\n",
		log_id(index.module), log_id(root), GetSize(candidate.removed), candidate.added_count());
	candidate.commit();
	return true;
}

struct ModuloRelation
{
	SigSpec base;
	Const residue, upper;
	pool<Cell *> region;
	bool selection = false;
};

struct ModuloTrace
{
	PmuxCoarseIndex &index;
	const Const modulus;
	std::optional<int> power_of_two;
	int remaining = 4096;
	pool<Cell *> active;

	ModuloTrace(PmuxCoarseIndex &index, const Const &modulus) : index(index), modulus(modulus)
	{
		int power;
		if (SigSpec(modulus).is_onehot(&power))
			power_of_two = power;
	}

	std::vector<ModuloRelation> trace(SigSpec signal, int depth = 0)
	{
		if (signal.empty() || (remaining -= GetSize(signal)) < 0)
			return {};
		signal = trim_zero_extension(signal);
		int width = GetSize(signal);
		Const upper(State::S0, width);
		for (int i = 0; i < width; i++)
			if (signal[i] != State::S0)
				upper.set(i, State::S1);
		// The signal itself is also a possible shared base, including when it has an offset from a deeper base.
		std::vector<ModuloRelation> relations;
		relations.push_back({signal, Const(State::S0, GetSize(modulus)), std::move(upper), {}, false});
		if (depth >= 16)
			return relations;

		Cell *driver = index.driver(signal[0]);
		if (!driver || !driver->type.in(ID($add), ID($pos), ID($mux), ID($pmux)) || !index.editable(driver))
			return relations;
		auto output = index.port(driver, ID::Y);
		if (GetSize(output) < width || output.extract(0, width) != signal)
			return relations;
		if (!active.insert(driver).second)
			return {};
		auto expanded = driver->type.in(ID($add), ID($pos))
			? trace_offset(driver, width, depth) : trace_selection(driver, width, depth);
		active.erase(driver);
		for (auto &relation : expanded) {
			relation.region.insert(driver);
			relations.push_back(std::move(relation));
		}
		return relations;
	}

	std::vector<ModuloRelation> trace_offset(Cell *driver, int width, int depth)
	{
		bool unary = driver->type == ID($pos);
		if (pmux_is_signed_port(driver, ID::A) && (unary || pmux_is_signed_port(driver, ID::B)))
			return {};
		SigSpec base = index.port(driver, ID::A);
		if (unary)
			return trace(base.extract(0, std::min(width, GetSize(base))), depth + 1);
		SigSpec offset = index.port(driver, ID::B);
		if (base.is_fully_const() && !offset.is_fully_const())
			std::swap(base, offset);
		if (offset.empty() || !offset.is_fully_def() || (remaining -= GetSize(offset)) < 0)
			return {};

		Const capacity(State::S0, width + 1);
		capacity.set(width, State::S1);
		Const increment = offset.as_const();
		bool wrap_preserves_residue = power_of_two && *power_of_two <= width;
		std::vector<ModuloRelation> relations;
		for (auto &relation : trace(base, depth + 1)) {
			int calc_width = std::max({width, GetSize(increment), GetSize(modulus), GetSize(relation.upper)}) + 1;
			auto sum = const_add(relation.upper, increment, false, false, calc_width);
			bool no_wrap = const_lt(sum, capacity, false, false, 1).as_bool();
			if (!no_wrap && !wrap_preserves_residue)
				continue;
			relation.upper = no_wrap ? std::move(sum) : Const(State::S1, width);
			auto accumulated = const_add(relation.residue, increment, false, false, calc_width);
			relation.residue = const_mod(accumulated, modulus, false, false, GetSize(modulus));
			relations.push_back(std::move(relation));
		}
		return relations;
	}

	std::vector<ModuloRelation> trace_selection(Cell *driver, int width, int depth)
	{
		int count = GetSize(driver->getPort(ID::S));
		if (count == 0 || count > pmux_max_rows)
			return {};

		std::vector<ModuloRelation> relations;
		bool first = true;
		for (const auto &branch : arithmetic_arms(index, driver, width, count)) {
			if (branch.is_fully_const() && branch.as_const().is_fully_undef_x_only())
				continue;
			auto alternatives = trace(branch, depth + 1);
			if (first) {
				relations = std::move(alternatives);
				first = false;
			} else {
				std::vector<ModuloRelation> intersection;
				for (auto &relation : relations) {
					auto other = std::find_if(alternatives.begin(), alternatives.end(), [&](const ModuloRelation &candidate) {
						return relation.base == candidate.base && relation.residue == candidate.residue;
					});
					if (other == alternatives.end())
						continue;
					if (const_lt(relation.upper, other->upper, false, false, 1).as_bool())
						relation.upper = other->upper;
					relation.region.insert(other->region.begin(), other->region.end());
					intersection.push_back(std::move(relation));
				}
				relations = std::move(intersection);
			}
			if (relations.empty())
				break;
		}
		for (auto &relation : relations)
			relation.selection = true;
		return relations;
	}
};

bool rewrite_modulo(PmuxCoarseIndex &index, Cell *root)
{
	if (!index.editable(root) || (pmux_is_signed_port(root, ID::A) && pmux_is_signed_port(root, ID::B)))
		return false;
	SigSpec modulus = index.port(root, ID::B);
	if (modulus.empty() || GetSize(modulus) > 4096 || !modulus.is_fully_def() || modulus.is_fully_zero())
		return false;
	SigSpec original = index.port(root, ID::A);
	ModuloTrace tracer{index, trim_zero_extension(modulus).as_const()};
	auto relations = tracer.trace(original);
	if (tracer.remaining < 0)
		return false;
	// Prefer deeper bases to the original signal.
	for (auto &relation : relations | std::views::reverse) {
		if (!relation.selection || !relation.residue.is_fully_zero() || relation.base == original)
			continue;
		relation.region.insert(root);
		PmuxRewrite candidate(index.module, index, "arith_modulo_congruence");
		SigSpec result(candidate.staging.addWire(NEW_ID, GetSize(root->getPort(ID::Y))));
		Cell *replacement = candidate.staging.addCell(NEW_ID, root->type);
		replacement->attributes = root->attributes;
		replacement->parameters = root->parameters;
		replacement->setPort(ID::A, relation.base);
		replacement->setPort(ID::B, modulus);
		replacement->setPort(ID::Y, result);
		replacement->setParam(ID::A_WIDTH, GetSize(relation.base));
		candidate.connect(root->getPort(ID::Y), result);
		candidate.find_removable(relation.region);
		if (!candidate.removed.count(root) || (GetSize(relation.base) >= GetSize(original) && candidate.removed.size() == 1) ||
				!candidate.validate())
			continue;
		log("  Reducing constant modulo at %s.%s (%d cells removed, %d added).\n",
			log_id(index.module), log_id(root), GetSize(candidate.removed), candidate.added_count());
		candidate.commit();
		return true;
	}
	return false;
}

struct OptPmuxArithPass : public Pass
{
	OptPmuxArithPass() : Pass("opt_pmux_arith", "simplify and share modular arithmetic around selections") {}

	void help() override
	{
		log("\n");
		log("    opt_pmux_arith [selection]\n");
		log("\n");
		log("Simplify additions and subtractions modulo the result width and share\n");
		log("arithmetic across $mux and $pmux branches by eliminating redundant operators.\n");
		log("Reduce unsigned constant modulo by proving congruence across branches.\n");
		log("Replace three-way comparison selections computing a minimum or maximum.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		pool<IdString> instantiated;
		for (Module *module : design->modules())
			for (Cell *cell : module->cells())
				if (design->module(cell->type))
					instantiated.insert(cell->type);
		pmux_run_pass(design, "opt_pmux_arith", "Executing OPT_PMUX_ARITH pass.\n", [&](Module *module) {
			PmuxCoarseIndex index(module);
			bool external_inputs = !instantiated.count(module->name);
			int changes = 0;
			auto run = [&](auto match, auto rewrite, bool selections_first = false) {
				std::vector<std::pair<bool, IdString>> names;
				for (auto cell : module->selected_cells())
					if (match(cell))
						names.emplace_back(selections_first && arithmetic_type(cell->type), cell->name);
				std::ranges::sort(names, [](const auto &a, const auto &b) {
					return a.first != b.first ? a.first < b.first : a.second.lt_by_name(b.second);
				});
				for (const auto &root : names)
					if (auto cell = module->cell(root.second))
						changes += rewrite(index, cell);
			};
			run([](Cell *cell) { return cell->type.in(ID($mod), ID($modfloor)); }, rewrite_modulo);
			run([](Cell *cell) { return cell->type == ID($pmux); }, rewrite_extremum);
			run([](Cell *cell) { return cell->type == ID($pmux) && GetSize(cell->getPort(ID::S)) >= 2; },
					[=](PmuxCoarseIndex &index, Cell *cell) {
						return rewrite_arithmetic(index, cell, external_inputs, ArithmeticTransform::ExcludedTerm);
					});
			run([](Cell *cell) { return cell->type.in(ID($mux), ID($pmux)) || arithmetic_type(cell->type); },
					[=](PmuxCoarseIndex &index, Cell *cell) {
						return rewrite_arithmetic(index, cell, external_inputs, ArithmeticTransform::CommonColumns);
					}, true);
			return changes;
		});
	}
} OptPmuxArithPass;

PRIVATE_NAMESPACE_END

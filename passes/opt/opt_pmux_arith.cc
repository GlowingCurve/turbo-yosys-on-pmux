#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "pmux_rewrite.h"

#include <algorithm>
#include <array>
#include <map>
#include <memory>
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

SigSpec trim_zero_extension(SigSpec value)
{
	int width = GetSize(value);
	while (width > 1 && value[width - 1] == State::S0)
		width--;
	return value.extract(0, width);
}

struct BinaryArithmeticInputs
{
	PmuxCoarseIndex &index;
	bool external_inputs;
	int remaining = 65536;
	pool<Cell *> active;
	dict<Cell *, bool> checked;

	BinaryArithmeticInputs(PmuxCoarseIndex &index, bool external_inputs) : index(index), external_inputs(external_inputs) {}

	bool check(const SigSpec &value, int depth = 0)
	{
		if (depth > 128)
			return false;
		for (SigBit bit : value) {
			if (--remaining < 0)
				return false;
			if (!bit.wire) {
				if (bit != State::S0 && bit != State::S1)
					return false;
				continue;
			}
			Cell *driver = index.driver(bit);
			if (driver ? !check_driver(driver, depth) : !(external_inputs && index.module_input(bit)))
				return false;
		}
		return true;
	}

	bool check_driver(Cell *cell, int depth)
	{
		if (checked.count(cell))
			return checked.at(cell);
		if (!cell->type.in(ID($add), ID($sub), ID($neg), ID($mul), ID($not), ID($and), ID($or), ID($xor), ID($xnor),
				ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and), ID($logic_or),
				ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor),
				ID($mux), ID($slice), ID($concat)) || !active.insert(cell).second)
			return false;
		bool defined = true;
		for (const auto &[name, input] : cell->connections())
			if (cell->input(name) && !check(index.sigmap(input), depth + 1)) {
				defined = false;
				break;
			}
		active.erase(cell);
		checked[cell] = defined;
		return defined;
	}
};

struct ArithmeticRewrite
{
	PmuxCoarseIndex &index;
	int width;
	int remaining = 2048;
	pool<Cell *> region;
	bool full_width_result = false;

	ArithmeticRewrite(PmuxCoarseIndex &index, int width) : index(index), width(width) {}

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
			SigSpec b;
			bool is_signed = driver->getParam(ID::A_SIGNED).as_bool();
			if (driver->type != ID($neg)) {
				b = index.port(driver, ID::B);
				is_signed &= driver->getParam(ID::B_SIGNED).as_bool();
			}
			SigSpec output = index.port(driver, ID::Y);
			const int output_width = GetSize(output);
			const int compared_width = std::min(output_width, width);
			bool matches = output.extract(0, compared_width) == value.extract(0, compared_width);
			if (output_width < width) {
				// A narrowed result can be widened only when the original operation cannot overflow.
				bool signed_extension = is_signed;
				bool zero_extension = !is_signed && driver->type == ID($add);
				matches &= (signed_extension || zero_extension) && output_width > std::max(GetSize(a), GetSize(b));
				output.extend_u0(width, signed_extension);
				matches &= output == value;
			}
			if (matches) {
				if (depth == 0)
					full_width_result = output_width >= width;
				region.insert(driver);
				a.extend_u0(width, is_signed);
				if (driver->type == ID($neg))
					return expand(a, -sign, expression, depth + 1);
				b.extend_u0(width, is_signed);
				return expand(a, sign, expression, depth + 1) &&
					expand(b, driver->type == ID($sub) ? -sign : sign, expression, depth + 1);
			}
		}

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

void add_column(ArithmeticPlan &plan, const std::vector<SigSpec> &values, const std::vector<bool> &defined, bool subtract)
{
	int width = 0;
	for (int i = 0; i < GetSize(values); i++)
		if (defined[i])
			width = std::max(width, GetSize(values[i]));

	std::vector<SigSpec> padded;
	for (auto value : values) {
		value.extend_u0(width);
		padded.push_back(std::move(value));
	}

	int first = std::find(defined.begin(), defined.end(), true) - defined.begin();
	ArithmeticColumn column{padded[first], {}, {}, subtract};
	dict<SigSpec, int> lanes;
	for (int bit = 0; bit < width; bit++) {
		SigSpec lane;
		bool common = true;
		for (int branch = 0; branch < GetSize(values); branch++) {
			const SigSpec &value = padded[branch];
			common &= !defined[branch] || value[bit] == column.operand[bit];
			lane.append(defined[branch] ? value[bit] : SigBit(State::Sx));
		}
		if (common)
			continue;

		auto [slot, inserted] = lanes.emplace(lane, GetSize(lanes));
		column.varying_bits.emplace_back(bit, slot->second);
		column.operand[bit] = State::S0;
		if (inserted) {
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
		add_column(plan, values, defined, subtract);
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

void improve_three_term_columns(ArithmeticPlan &best, std::vector<std::vector<SigSpec>> &terms, const std::vector<bool> &defined)
{
	std::vector<int> branches;
	int width = 0;
	for (int i = 0; i < GetSize(terms); i++) {
		if (!defined[i])
			continue;
		if (GetSize(terms[i]) != 3 || GetSize(branches) == 4)
			return;
		branches.push_back(i);
		for (const auto &term : terms[i])
			width = std::max(width, GetSize(term));
	}
	if (GetSize(branches) < 2)
		return;
	int combinations = 1;
	for (int i = 1; i < GetSize(branches); i++)
		combinations *= 6;
	constexpr int permutation_work_limit = 1 << 18;
	if (int64_t{3} * combinations * width * GetSize(terms) > permutation_work_limit)
		return;

	auto best_width = selected_width(best);
	// 整体交换三列不会改变选择规模，因此固定第一个已定义分支。
	auto enumerate = [&](auto &self, int branch) -> void {
		if (branch == GetSize(branches)) {
			auto candidate = make_term_columns(terms, defined, 3, false);
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
	for (int sign : {1, -1}) {
		// Emit common terms before allocating selector inputs to the remaining terms.
		int first = std::find(defined.begin(), defined.end(), true) - defined.begin();
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
			improve_three_term_columns(columns, terms, defined);
		for (auto &column : columns)
			plan.push_back(std::move(column));
	}

	std::vector<SigSpec> offsets;
	for (auto &expression : expressions)
		offsets.push_back(trim_zero_extension(expression.offset));
	add_column(plan, offsets, defined, false);
	return plan;
}

ArithmeticPlan make_exclusion_plan(const std::vector<ArithmeticExpression> &expressions, const std::vector<bool> &defined,
		BinaryArithmeticInputs &binary)
{
	std::set<SigSpec> total;
	std::vector<SigSpec> offsets;
	for (int i = 0; i < GetSize(expressions); i++) {
		offsets.push_back(trim_zero_extension(expressions[i].offset));
		if (!defined[i])
			continue;
		for (auto &[term, coefficient] : expressions[i].terms) {
			if (coefficient != 1)
				return {};
			total.insert(term);
		}
	}
	if (GetSize(total) < 3)
		return {};
	// The total includes terms unused by individual branches. They must be binary
	// so an unknown term cannot contaminate a branch that originally omitted it.
	for (const auto &term : total)
		if (!binary.check(term))
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
	add_column(plan, excluded, defined, true);
	add_column(plan, offsets, defined, false);
	return plan;
}

bool prepare_arithmetic_rewrite(PmuxRewrite &candidate, PmuxCoarseIndex &index, Cell *root,
		const pool<Cell *> &region, const SigSpec &result)
{
	pool<SigBit> inputs, outputs;
	auto record_inputs = [&](const SigSpec &signal) {
		for (auto bit : signal)
			if (bit.wire && bit.wire->module == index.module)
				inputs.insert(bit);
	};
	for (auto cell : candidate.staging.cells())
		for (const auto &[port, signal] : cell->connections())
			if (cell->input(port))
				record_inputs(signal);
	record_inputs(result);
	for (auto bit : index.port(root, ID::Y))
		outputs.insert(bit);
	candidate.removed = index.removable(region, {}, outputs, inputs);
	if (!candidate.removed.count(root))
		return false;
	candidate.connect(root->getPort(ID::Y), result);
	return true;
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
		return cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
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
		// 相等关系允许同时扩展两个已经等宽的操作数。
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
		if (strict_comparison(cell) || cell->type == ID($eq)) {
			if (auto ordering = relation(cell)) {
				Values values = {State::S0, State::S0, State::S0, State::Sx, State::Sx};
				values[*ordering] = State::S1;
				if (*ordering == equal)
					values[unknown_different] = State::S0;
				else
					strict_selects.emplace_back(*ordering, bit);
				seen[*ordering] = true;
				region.insert(cell);
				evaluated.emplace(bit, values);
				return values;
			}
		}
		if (!predicate_gate(cell))
			return std::nullopt;
		std::array<Const, row_count> a, b;
		for (auto port : {ID::A, ID::B}) {
			if (!cell->hasPort(port))
				continue;
			auto &operand = port == ID::A ? a : b;
			for (auto input : index.port(cell, port)) {
				auto values = evaluate(input, depth + 1);
				if (!values)
					return std::nullopt;
				for (int row = 0; row < row_count; ++row)
					operand[row].append((*values)[row]);
			}
		}
		Values values;
		for (int row = 0; row < row_count; ++row)
			values[row] = CellTypes::eval(cell, a[row], b[row])[0];
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
	if (root->type != ID($pmux) || !index.editable(root))
		return false;
	auto select = index.port(root, ID::S);
	int width = GetSize(root->getPort(ID::Y));
	if (width == 0 || width > 4096 || select.empty() || GetSize(select) > 16)
		return false;
	auto fallback = index.port(root, ID::A), cases = index.port(root, ID::B);
	if (GetSize(fallback) != width || GetSize(cases) != width * GetSize(select))
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

	std::array<SigSpec, 3> selected;
	for (int row = 0; row < ExtremumPredicates::row_count; ++row) {
		auto choice = choices[row].as_const();
		bool binary_row = row < ExtremumPredicates::unknown_different;
		int branch = -1;
		if (!choice.is_fully_zero() && !choice.is_onehot(&branch)) {
			if (binary_row)
				return false;
			continue;
		}
		auto arm = branch < 0 ? fallback : cases.extract(branch * width, width);
		if (binary_row)
			selected[row] = arm;
		// 只有原选择全部未定义时，才能细化未知比较下的输出。
		else if (!arm.is_fully_const() || !arm.as_const().is_fully_undef_x_only())
			return false;
	}

	for (bool sign_extend : {predicates.signed_order, false}) {
		auto lhs = predicates.lhs, rhs = predicates.rhs;
		lhs.extend_u0(width, sign_extend);
		rhs.extend_u0(width, sign_extend);
		bool minimum = selected[ExtremumPredicates::less] == lhs && selected[ExtremumPredicates::greater] == rhs;
		bool maximum = selected[ExtremumPredicates::less] == rhs && selected[ExtremumPredicates::greater] == lhs;
		if ((!minimum && !maximum) || !match_equal_arm(index, selected[ExtremumPredicates::equal], lhs, rhs, predicates.region))
			continue;
		predicates.region.insert(root);
		std::unique_ptr<PmuxRewrite> best;
		bool best_uses_less = false;
		for (auto [relation, control] : predicates.strict_selects) {
			bool uses_less = relation == ExtremumPredicates::less;
			bool select_lhs = minimum == uses_less;
			auto candidate = std::make_unique<PmuxRewrite>(index.module, index, "arith-extremum");
			auto result = candidate->staging.Mux(NEW_ID, select_lhs ? rhs : lhs, select_lhs ? lhs : rhs,
					control, root->get_src_attribute());
			if (!prepare_arithmetic_rewrite(*candidate, index, root, predicates.region, result))
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
					? module->Mux(NEW_ID, column.variants.front(), cases, select)
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

bool rewrite_arithmetic(PmuxCoarseIndex &index, Cell *root, bool external_inputs)
{
	if (!index.editable(root))
		return false;
	SigSpec output = index.port(root, ID::Y);
	int width = GetSize(output);
	ArithmeticRewrite rewrite{index, width};
	BinaryArithmeticInputs binary{index, external_inputs};
	SigSpec select;
	std::vector<SigSpec> branches;
	if (arithmetic_type(root->type)) {
		branches.push_back(output);
	} else {
		select = index.port(root, ID::S);
		SigSpec data = index.port(root, ID::B);
		int count = GetSize(select);
		if (count == 0 || count > 64 || GetSize(data) / count != width || GetSize(data) % count != 0)
			return false;
		branches.push_back(index.port(root, ID::A));
		for (int i = 0; i < count; i++)
			branches.push_back(data.extract(i * width, width));
		if (std::none_of(branches.begin(), branches.end(), [&](const SigSpec &branch) {
			Cell *driver = branch.empty() ? nullptr : index.driver(branch[0]);
			return driver && arithmetic_type(driver->type);
		}))
			return false;
		// A binary mux merges its branches bit by bit for an unknown selector.
		// Selecting an arithmetic operand before its operation may lose known bits.
		if (root->type == ID($mux) && !binary.check(select))
			return false;
	}

	std::vector<ArithmeticExpression> expressions;
	std::vector<bool> defined;
	for (const SigSpec &branch : branches) {
		if (GetSize(branch) != width)
			return false;
		expressions.emplace_back(width);
		bool unspecified = branch.is_fully_const() && branch.as_const().is_fully_undef_x_only();
		defined.push_back(!unspecified);
		if (unspecified)
			continue;
		rewrite.full_width_result = false;
		if (!rewrite.expand(branch, 1, expressions.back()))
			return false;
		// Full-width arithmetic is all X when an input is unknown. An unexpanded
		// or zero-extended branch may still have defined bits in that situation.
		if (!select.empty() && !rewrite.full_width_result && !binary.check(branch))
			return false;
	}
	if (rewrite.region.empty())
		return false;
	if (select.empty() && !expressions.front().simplified && !expressions.front().terms.empty())
		return false;
	rewrite.region.insert(root);

	auto apply = [&](const ArithmeticPlan &plan, const char *rule) {
		PmuxRewrite candidate(index.module, index, rule);
		auto result = emit_arithmetic(&candidate.staging, plan, select, width);
		if (!prepare_arithmetic_rewrite(candidate, index, root, rewrite.region, result))
			return false;
		// 保留外部仍在使用的生产者，并确认本次重建能消除旧算术。
		if (candidate.added_count() && std::none_of(candidate.removed.begin(), candidate.removed.end(), [&](Cell *cell) {
				return cell != root && arithmetic_type(cell->type);
			}))
			return false;
		if (!candidate.validate())
			return false;
		log("  Rewriting arithmetic at %s.%s (%d cells removed, %d added).\n",
			log_id(index.module), log_id(root), GetSize(candidate.removed), candidate.added_count());
		candidate.commit();
		return true;
	};
	if (GetSize(select) >= 2) {
		ArithmeticPlan exclusion = make_exclusion_plan(expressions, defined, binary);
		if (!exclusion.empty() && apply(exclusion, "arith-excluded-term"))
			return true;
	}
	return apply(make_column_plan(expressions, defined), "arith-common-columns");
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
	int power_of_two = -1;
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
		if (driver && driver->type.in(ID($add), ID($pos), ID($mux), ID($pmux)) && index.editable(driver)) {
			SigSpec output = index.port(driver, ID::Y);
			if (GetSize(output) >= width && output.extract(0, width) == signal) {
				if (!active.insert(driver).second)
					return {};
				auto expanded = driver->type.in(ID($add), ID($pos))
					? trace_offset(driver, width, depth)
					: trace_selection(driver, width, GetSize(output), depth);
				active.erase(driver);
				for (auto &relation : expanded) {
					relation.region.insert(driver);
					relations.push_back(std::move(relation));
				}
			}
		}
		return relations;
	}

	std::vector<ModuloRelation> trace_offset(Cell *driver, int width, int depth)
	{
		bool unary = driver->type == ID($pos);
		if (driver->getParam(ID::A_SIGNED).as_bool() && (unary || driver->getParam(ID::B_SIGNED).as_bool()))
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
		bool wrap_preserves_residue = power_of_two >= 0 && power_of_two <= width;
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

	std::vector<ModuloRelation> trace_selection(Cell *driver, int width, int branch_width, int depth)
	{
		SigSpec select = index.port(driver, ID::S);
		SigSpec fallback = index.port(driver, ID::A);
		SigSpec data = index.port(driver, ID::B);
		int count = GetSize(select);
		if (count == 0 || count > 64 || GetSize(fallback) != branch_width ||
				GetSize(data) / count != branch_width || GetSize(data) % count != 0)
			return {};

		std::vector<ModuloRelation> relations;
		bool first = true;
		for (int i = -1; i < count; i++) {
			SigSpec branch = i == -1 ? fallback.extract(0, width) : data.extract(i * branch_width, width);
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
	if (!index.editable(root) || (root->getParam(ID::A_SIGNED).as_bool() && root->getParam(ID::B_SIGNED).as_bool()))
		return false;
	SigSpec modulus = index.port(root, ID::B);
	if (modulus.empty() || GetSize(modulus) > 4096 || !modulus.is_fully_def() || modulus.is_fully_zero())
		return false;
	SigSpec original = index.port(root, ID::A);
	ModuloTrace tracer{index, trim_zero_extension(modulus).as_const()};
	auto relations = tracer.trace(original);
	if (tracer.remaining < 0)
		return false;
	// 追踪先记录当前信号，再记录更深的基底。
	for (auto it = relations.rbegin(); it != relations.rend(); ++it) {
		auto &relation = *it;
		if (!relation.selection || !relation.residue.is_fully_zero() || relation.base == original)
			continue;
		relation.region.insert(root);
		PmuxRewrite candidate(index.module, index, "arith-modulo-congruence");
		SigSpec result(candidate.staging.addWire(NEW_ID, GetSize(root->getPort(ID::Y))));
		Cell *replacement = candidate.staging.addCell(NEW_ID, root);
		replacement->setPort(ID::A, relation.base);
		replacement->setPort(ID::B, modulus);
		replacement->setPort(ID::Y, result);
		replacement->setParam(ID::A_WIDTH, GetSize(relation.base));
		if (!prepare_arithmetic_rewrite(candidate, index, root, relation.region, result))
			continue;
		if (GetSize(relation.base) >= GetSize(original) && candidate.removed.size() == 1)
			continue;
		if (!candidate.validate())
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
		log_header(design, "Executing OPT_PMUX_ARITH pass.\n");
		extra_args(args, 1, design);
		if (pmux_coarse_observes_undef(design))
			return;
		pool<IdString> instantiated;
		for (Module *module : design->modules())
			for (Cell *cell : module->cells())
				if (design->module(cell->type))
					instantiated.insert(cell->type);
		for (Module *module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			PmuxCoarseIndex index(module);
			std::vector<IdString> modulos, selections, operators;
			for (Cell *cell : module->selected_cells()) {
				if (cell->type.in(ID($mod), ID($modfloor)))
					modulos.push_back(cell->name);
				else if (cell->type.in(ID($mux), ID($pmux)))
					selections.push_back(cell->name);
				else if (arithmetic_type(cell->type))
					operators.push_back(cell->name);
			}
			std::sort(modulos.begin(), modulos.end());
			std::sort(selections.begin(), selections.end());
			std::sort(operators.begin(), operators.end());
			for (IdString name : modulos) {
				Cell *cell = module->cell(name);
				if (cell && rewrite_modulo(index, cell))
					design->scratchpad_set_bool("opt.did_something", true);
			}
			selections.insert(selections.end(), operators.begin(), operators.end());
			bool external_inputs = !instantiated.count(module->name);
			for (IdString name : selections) {
				Cell *cell = module->cell(name);
				if (cell && (rewrite_extremum(index, cell) || rewrite_arithmetic(index, cell, external_inputs)))
					design->scratchpad_set_bool("opt.did_something", true);
			}
		}
	}
} OptPmuxArithPass;

PRIVATE_NAMESPACE_END

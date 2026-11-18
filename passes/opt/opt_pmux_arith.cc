/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  薛朝意
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

// 优化方法层的算术化简。检查分支间的取模、极值和加减关系，提取公共算术项。

#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "passes/opt/pmux_common.h"
#include "passes/opt/pmux_rewrite.h"

#include <algorithm>
#include <array>
#include <map>
#include <memory>
#include <ranges>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 记录一个分支中各算术项的系数和常量偏移。
struct ArithmeticExpression {
	std::map<SigSpec, int> terms;
	Const offset;
	bool has_offset = false;
	bool simplified = false;

	// 以结果位宽初始化分支的常量偏移。
	explicit ArithmeticExpression(int width) : offset(0, width) {}
};

// 记录公共操作数以及需要按分支选择的数据位。
struct ArithmeticColumn {
	SigSpec operand;
	std::vector<SigSpec> variants;
	std::vector<std::pair<int, int>> varying_bits;
	bool subtract;
};

using ArithmeticPlan = std::vector<ArithmeticColumn>;

// 识别能够展开为带符号系数的加减运算。
bool arithmetic_type(IdString type) { return type.in(ID($add), ID($sub), ID($neg)); }

// 移除连续的高位零，保留至少一个输入位。
SigSpec trim_zero_extension(const SigSpec &value)
{
	int width = GetSize(value);
	while (width > 1 && value[width - 1] == State::S0)
		width--;
	return value.extract(0, width);
}

// 收集算术表达式并限制递归深度和访问量。
struct ArithmeticRewrite {
	PmuxCoarseIndex index;
	int width;
	bool external_inputs, has_selector;
	int remaining = 2048;
	int binary_remaining = 65536;
	pool<Cell *> region;
	pool<Cell *> binary_cells, active;

	// 设置表达式位宽和模块输入的处理条件。
	ArithmeticRewrite(PmuxCoarseIndex &index, int width, bool external_inputs, bool has_selector)
	    : index(index), width(width), external_inputs(external_inputs), has_selector(has_selector)
	{
	}

	// 检查输入中的每个位是否可证明为二值。
	bool binary(const SigSpec &value, int depth = 0)
	{
		if (depth > 128)
			return false;
		binary_remaining -= GetSize(value);
		if (binary_remaining < 0)
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
			if (!cell->type.in(ID($add), ID($sub), ID($neg), ID($mul), ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($eq), ID($ne),
					   ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and), ID($logic_or), ID($reduce_and),
					   ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor), ID($mux), ID($slice), ID($concat)) ||
			    !active.insert(cell).second)
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

	// 将当前常量累加到表达式的固定偏移量。
	bool expand_constant(const SigSpec &value, int sign, ArithmeticExpression &expression)
	{
		if (!value.is_fully_def())
			return false;
		expression.simplified |= expression.has_offset || value.is_fully_zero();
		expression.has_offset = true;
		expression.offset = sign > 0 ? const_add(expression.offset, value.as_const(), false, false, width)
					     : const_sub(expression.offset, value.as_const(), false, false, width);
		return true;
	}

	// 在结果位宽内展开分支表达式并累计同类项。
	bool expand(SigSpec value, int sign, ArithmeticExpression &expression, int depth = 0)
	{
		--remaining;
		if (remaining < 0 || depth > 12 || GetSize(expression.terms) > 16)
			return false;
		if (value.is_fully_const())
			return expand_constant(value, sign, expression);

		Cell *driver = index.driver(value[0]);
		if (driver && arithmetic_type(driver->type) && index.editable(driver)) {
			SigSpec a = index.port(driver, ID::A);
			bool unary = driver->type == ID($neg);
			auto b = unary ? SigSpec() : index.port(driver, ID::B);
			bool is_signed = pmux_cell_signed(driver);
			SigSpec output = index.port(driver, ID::Y);
			const int output_width = GetSize(output);
			const int compared_width = std::min(output_width, width);
			bool matches = output.extract(0, compared_width) == value.extract(0, compared_width);
			if (output_width < width) {
				// 原运算不会溢出时，才可扩展较窄的结果。
				matches &= (is_signed || driver->type == ID($add)) && output_width > std::max(GetSize(a), GetSize(b));
				output.extend_u0(width, is_signed);
				matches &= output == value;
			}
			if (matches) {
				// 运算结果含未知值时，扩展位仍可能确定。
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

// 提取一列公共数据位，只为不同的位生成选择输入。
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

// 将各个分支中相同位置的算术项组合成列。
ArithmeticPlan make_term_columns(const std::vector<std::vector<SigSpec>> &terms, const std::vector<bool> &defined, int count, bool subtract)
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

// 计算候选方案需要选择的数据位数和单元数。
std::pair<int, int> selected_width(const ArithmeticPlan &plan)
{
	int bits = 0;
	int cells = 0;
	for (const auto &column : plan)
		if (!column.variants.empty()) {
			bits += GetSize(column.variants.front());
			cells++;
		}
	return {bits, cells};
}

// 固定首个分支的顺序，枚举其余分支中算术项的排列。
void enumerate_terms(std::vector<std::vector<SigSpec>> &terms, const std::vector<bool> &defined, const std::vector<int> &branches, int columns,
		     int branch, ArithmeticPlan &best, std::pair<int, int> &best_width)
{
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
		enumerate_terms(terms, defined, branches, columns, branch + 1, best, best_width);
	} while (std::next_permutation(row.begin(), row.end()));
}

// 在规定预算内调整分支中各算术项的排列。
void improve_term_columns(ArithmeticPlan &best, std::vector<std::vector<SigSpec>> &terms, const std::vector<bool> &defined, int columns)
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
	// 同时重排全部分支的项不会改变选择器代价。
	enumerate_terms(terms, defined, branches, columns, 1, best, best_width);
}

// 分别整理加法项和减法项，提取公共操作数。
ArithmeticPlan make_column_plan(std::vector<ArithmeticExpression> expressions, const std::vector<bool> &defined)
{
	ArithmeticPlan plan;
	int first = std::find(defined.begin(), defined.end(), true) - defined.begin();
	for (int sign : {1, -1}) {
		// 先提取公共项，再为其余项分配选择输入。
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

// 识别可以由总和减去缺项得到的各分支。
ArithmeticPlan make_exclusion_plan(const std::vector<ArithmeticExpression> &expressions, const std::vector<bool> &defined, ArithmeticRewrite &rewrite)
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
	// 总和包含原分支未使用的项，必须确认这些项为二值，避免未知值进入结果。
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

// 计算比较条件在五种操作数关系下的结果。
struct ExtremumPredicates {
	enum Row { less, equal, greater, unknown_different, unknown, row_count };
	using Values = std::array<State, row_count>;

	PmuxCoarseIndex index;
	SigSpec lhs, rhs;
	bool signed_order;
	std::vector<std::pair<Row, SigBit>> strict_selects;
	pool<Cell *> region;
	dict<SigBit, Values> evaluated;
	std::array<bool, 3> seen{};
	int remaining = 512;

	// 识别严格大于或小于比较。
	static bool strict_comparison(Cell *cell) { return cell->type.in(ID($lt), ID($gt)); }

	// 识别极值选择条件中允许出现的逻辑单元。
	static bool predicate_gate(Cell *cell)
	{
		return cell->type.in(ID($eq), ID($ne), ID($not), ID($logic_not), ID($and), ID($or), ID($xor), ID($xnor), ID($logic_and),
				     ID($logic_or), ID($reduce_bool), ID($reduce_or), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor));
	}

	// 沿选择信号输入查找参与大小判断的比较器。
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

	// 判断比较运算是否使用有符号操作数。
	static bool signed_comparison(Cell *cell) { return pmux_cell_signed(cell); }

	// 取得参照比较器的两个操作数及其符号属性。
	ExtremumPredicates(PmuxCoarseIndex &index, Cell *order)
	    : index(index), lhs(index.port(order, ID::A)), rhs(index.port(order, ID::B)), signed_order(signed_comparison(order))
	{
		int width = std::max(GetSize(lhs), GetSize(rhs));
		lhs.extend_u0(width, signed_order);
		rhs.extend_u0(width, signed_order);
	}

	// 判断当前比较器对应的操作数顺序与关系。
	std::optional<Row> relation(Cell *cell)
	{
		bool is_equal = cell->type == ID($eq);
		bool is_signed = signed_comparison(cell);
		if (!is_equal && is_signed != signed_order)
			return std::nullopt;
		auto a = index.port(cell, ID::A);
		auto b = index.port(cell, ID::B);
		int width = std::max(GetSize(a), GetSize(b));
		if (a.empty() || b.empty() || width > 4096)
			return std::nullopt;
		a.extend_u0(width, is_signed);
		b.extend_u0(width, is_signed);
		// 将比较器的两个输入按相同规则扩展。
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

	// 对各个比较关系分别计算逻辑门输入，并按四态语义求值。
	std::optional<Values> evaluate_gate(Cell *cell, int depth)
	{
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
		Values values;
		for (int row = 0; row < row_count; ++row)
			values[row] = CellTypes::eval(cell, a[row], b[row])[0];
		return values;
	}

	// 计算选择条件在各比较关系下的四态结果。
	std::optional<Values> evaluate(SigBit bit, int depth = 0)
	{
		if (depth > 12)
			return std::nullopt;
		--remaining;
		if (remaining < 0)
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
			auto gate = evaluate_gate(cell, depth);
			if (!gate)
				return std::nullopt;
			values = *gate;
		}
		region.insert(cell);
		evaluated.emplace(bit, values);
		return values;
	}
};

// 检查相等分支选择的数据是否与比较输入一致。
bool match_equal_arm(PmuxCoarseIndex &index, const SigSpec &value, const SigSpec &lhs, const SigSpec &rhs, pool<Cell *> &region)
{
	if (value == lhs || value == rhs)
		return true;
	auto cell = index.driver(value[0]);
	if (!cell || !cell->type.in(ID($and), ID($or)))
		return false;
	int width = GetSize(value);
	auto output = index.port(cell, ID::Y);
	auto a = index.port(cell, ID::A);
	auto b = index.port(cell, ID::B);
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
		auto left = padded(a);
		auto right = padded(b);
		if ((left == lhs || left == rhs) && (right == lhs || right == rhs)) {
			region.insert(cell);
			return true;
		}
	}
	return false;
}

// 检查小于、等于、大于，以及含未知位时确定不等或关系未定的两种情况。
bool extremum_arms(PmuxCoarseIndex &index, Cell *root, ExtremumPredicates &predicates, const SigSpec &select, int width,
		   std::array<SigSpec, 3> &selected)
{
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

	auto arms = PmuxChoice(index, root).all_arms(width);
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
		// 比较关系未确定时，原分支的全部数据位必须均为未知值。
		else if (!arm.is_fully_const() || !arm.as_const().is_fully_undef_x_only())
			return false;
	}
	return true;
}

// 对原有比较信号尝试二选一电路，优先保留可移除单元较多的构造。
bool emit_extremum(PmuxCoarseIndex &index, Cell *root, ExtremumPredicates &predicates, int width, const std::array<SigSpec, 3> &selected)
{
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
			auto result =
			  pmux_emit_mux(&candidate->staging, control, select_lhs ? rhs : lhs, select_lhs ? lhs : rhs, root->get_src_attribute());
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
		log_debug("  Rewriting extremum at %s.%s (%d cells removed, %d added).\n", log_id(index.module), log_id(root), GetSize(best->removed),
			  best->added_count());
		best->commit();
		return true;
	}
	return false;
}

// 识别比较选择结构并检查极值替换条件。
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
	std::array<SigSpec, 3> selected;
	return extremum_arms(index, root, predicates, select, width, selected) && emit_extremum(index, root, predicates, width, selected);
}

// 生成公共算术电路，把有差异的数据位接到选择器。
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
				SigSpec selected;
				if (GetSize(select) == 1)
					selected = pmux_emit_mux(module, select, column.variants.front(), column.variants.back());
				else
					selected = pmux_build_choice(module, select, column.variants, ID($pmux));
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

// 收集选择器分支，并检查未知选择位是否影响算术输出。
bool arithmetic_branches(PmuxCoarseIndex &index, Cell *root, ArithmeticRewrite &rewrite, SigSpec &select, std::vector<SigSpec> &branches)
{
	if (!rewrite.has_selector) {
		branches.push_back(index.port(root, ID::Y));
		return true;
	}
	select = index.port(root, ID::S);
	int count = GetSize(select);
	if (count == 0 || count > pmux_max_rows)
		return false;
	branches = PmuxChoice(index, root).all_arms(rewrite.width);
	if (std::none_of(branches.begin(), branches.end(), [&](const SigSpec &branch) {
		    Cell *driver = branch.empty() ? nullptr : index.driver(branch[0]);
		    return driver && arithmetic_type(driver->type);
	    }))
		return false;
	// 选择位未知时，二选一单元仍能保留两个分支中相同的位；提前选择操作数需要保证选择位为二值。
	if (root->type == ID($mux) && !rewrite.binary(select))
		return false;
	return true;
}

// 展开每个已定义分支，记录公共项和常量偏移。
bool expand_branches(ArithmeticRewrite &rewrite, const std::vector<SigSpec> &branches, std::vector<ArithmeticExpression> &expressions,
		     std::vector<bool> &defined)
{
	for (const SigSpec &branch : branches) {
		expressions.emplace_back(rewrite.width);
		bool unspecified = branch.is_fully_const() && branch.as_const().is_fully_undef_x_only();
		defined.push_back(!unspecified);
		if (unspecified)
			continue;
		if (!rewrite.expand(branch, 1, expressions.back()))
			return false;
	}
	return !rewrite.region.empty();
}

// 识别候选根单元并检查算术提取是否减少单元数。
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
	if (!arithmetic_branches(index, root, rewrite, select, branches))
		return false;

	std::vector<ArithmeticExpression> expressions;
	std::vector<bool> defined;
	if (!expand_branches(rewrite, branches, expressions, defined))
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
	log_debug("  Rewriting arithmetic at %s.%s (%d cells removed, %d added).\n", log_id(index.module), log_id(root), GetSize(candidate.removed),
		  candidate.added_count());
	candidate.commit();
	return true;
}

// 记录当前信号相对候选基数的余数与上界。
struct ModuloRelation {
	SigSpec base;
	Const residue, upper;
	pool<Cell *> region;
	bool selection = false;
};

// 在限定预算内沿数据通路计算可能的同余关系。
struct ModuloTrace {
	PmuxCoarseIndex index;
	const Const modulus;
	std::optional<int> power_of_two;
	int remaining = 4096;
	pool<Cell *> active;

	// 以目标模数和结果位宽初始化同余检查。
	ModuloTrace(PmuxCoarseIndex &index, const Const &modulus) : index(index), modulus(modulus)
	{
		int power;
		if (SigSpec(modulus).is_onehot(&power))
			power_of_two = power;
	}

	// 从输入信号向前追溯能够复用的同余基数。
	std::vector<ModuloRelation> trace(SigSpec signal, int depth = 0)
	{
		if (signal.empty())
			return {};
		remaining -= GetSize(signal);
		if (remaining < 0)
			return {};
		signal = trim_zero_extension(signal);
		int width = GetSize(signal);
		Const upper(State::S0, width);
		for (int i = 0; i < width; i++)
			if (signal[i] != State::S0)
				upper.set(i, State::S1);
		// 当前信号也可作为基数，与更深的基数一起参与比较。
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
		auto expanded = driver->type.in(ID($add), ID($pos)) ? trace_offset(driver, width, depth) : trace_selection(driver, width, depth);
		active.erase(driver);
		for (auto &relation : expanded) {
			relation.region.insert(driver);
			relations.push_back(std::move(relation));
		}
		return relations;
	}

	// 根据加减常量传播余数并检查溢出条件。
	std::vector<ModuloRelation> trace_offset(Cell *driver, int width, int depth)
	{
		bool unary = driver->type == ID($pos);
		if (pmux_cell_signed(driver))
			return {};
		SigSpec base = index.port(driver, ID::A);
		if (unary)
			return trace(base.extract(0, std::min(width, GetSize(base))), depth + 1);
		SigSpec offset = index.port(driver, ID::B);
		if (base.is_fully_const() && !offset.is_fully_const())
			std::swap(base, offset);
		if (offset.empty() || !offset.is_fully_def())
			return {};
		remaining -= GetSize(offset);
		if (remaining < 0)
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

	// 保留在每个已定义选择分支中都成立的同余关系。
	std::vector<ModuloRelation> trace_selection(Cell *driver, int width, int depth)
	{
		int count = GetSize(driver->getPort(ID::S));
		if (count == 0 || count > pmux_max_rows)
			return {};

		std::vector<ModuloRelation> relations;
		bool first = true;
		for (const auto &branch : PmuxChoice(index, driver).all_arms(width)) {
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

// 使用同余基数缩小无符号常量取模电路。
bool rewrite_modulo(PmuxCoarseIndex &index, Cell *root)
{
	if (!index.editable(root) || pmux_cell_signed(root))
		return false;
	SigSpec modulus = index.port(root, ID::B);
	if (modulus.empty() || GetSize(modulus) > 4096 || !modulus.is_fully_def() || modulus.is_fully_zero())
		return false;
	SigSpec original = index.port(root, ID::A);
	ModuloTrace tracer{index, trim_zero_extension(modulus).as_const()};
	auto relations = tracer.trace(original);
	if (tracer.remaining < 0)
		return false;
	// 优先检查沿数据输入追溯得到的基数。
	for (auto &relation : relations | std::views::reverse) {
		if (!relation.selection || !relation.residue.is_fully_zero() || relation.base == original)
			continue;
		relation.region.insert(root);
		PmuxRewrite candidate(index.module, index, "arith_modulo_congruence");
		SigSpec result(candidate.staging.addWire(NEW_ID, GetSize(root->getPort(ID::Y))));
		Cell *replacement = candidate.clone_cell(NEW_ID, root);
		replacement->setPort(ID::A, relation.base);
		replacement->setPort(ID::B, modulus);
		replacement->setPort(ID::Y, result);
		replacement->setParam(ID::A_WIDTH, GetSize(relation.base));
		candidate.connect(root->getPort(ID::Y), result);
		candidate.find_removable(relation.region);
		if (!candidate.removed.count(root) || (GetSize(relation.base) >= GetSize(original) && candidate.removed.size() == 1) ||
		    !candidate.validate())
			continue;
		log_debug("  Reducing constant modulo at %s.%s (%d cells removed, %d added).\n", log_id(index.module), log_id(root),
			  GetSize(candidate.removed), candidate.added_count());
		candidate.commit();
		return true;
	}
	return false;
}

// 按候选优先级和单元名称排序。提交改写后按名称重新查找单元。
template <typename Priority, typename Rewrite> int rewrite_sorted(PmuxCoarseIndex &index, Priority priority, Rewrite rewrite)
{
	std::vector<std::pair<int, IdString>> names;
	for (auto cell : index.module->selected_cells()) {
		int rank = priority(cell);
		if (rank >= 0)
			names.emplace_back(rank, cell->name);
	}
	std::ranges::sort(names, [](const auto &a, const auto &b) { return a.first != b.first ? a.first < b.first : a.second.lt_by_name(b.second); });
	int changes = 0;
	for (const auto &[rank, name] : names) {
		auto cell = index.module->cell(name);
		if (cell)
			changes += rewrite(index, cell);
	}
	return changes;
}

// 利用各个分支的同余关系缩短取模输入。
int simplify_congruent_modulo(PmuxCoarseIndex &index)
{
	return rewrite_sorted(index, [](Cell *cell) { return cell->type.in(ID($mod), ID($modfloor)) ? 0 : -1; }, rewrite_modulo);
}

// 将使用比较条件的极值选择化简为二选一。
int simplify_extremum_choices(PmuxCoarseIndex &index)
{
	return rewrite_sorted(index, [](Cell *cell) { return cell->type == ID($pmux) ? 0 : -1; }, rewrite_extremum);
}

// 将每个分支缺少一项的累加式改写为总和减去该项。
int rewrite_excluded_sum(PmuxCoarseIndex &index, bool external_inputs)
{
	auto priority = [](Cell *cell) { return cell->type == ID($pmux) && GetSize(cell->getPort(ID::S)) >= 2 ? 0 : -1; };
	return rewrite_sorted(index, priority, [external_inputs](PmuxCoarseIndex &index, Cell *cell) {
		return rewrite_arithmetic(index, cell, external_inputs, ArithmeticTransform::ExcludedTerm);
	});
}

// 提取分支间的公共算术项，优先处理选择器。
int share_common_arithmetic(PmuxCoarseIndex &index, bool external_inputs)
{
	auto priority = [](Cell *cell) {
		if (cell->type.in(ID($mux), ID($pmux)))
			return 0;
		return arithmetic_type(cell->type) ? 1 : -1;
	};
	return rewrite_sorted(index, priority, [external_inputs](PmuxCoarseIndex &index, Cell *cell) {
		return rewrite_arithmetic(index, cell, external_inputs, ArithmeticTransform::CommonColumns);
	});
}

// 对含算术运算的模块按固定顺序执行四项改写。
int optimize_arithmetic_module(Module *module, bool external_inputs)
{
	bool has_candidate = false;
	for (auto cell : module->cells())
		if (arithmetic_type(cell->type) || cell->type.in(ID($mod), ID($modfloor), ID($lt), ID($gt))) {
			has_candidate = true;
			break;
		}
	if (!has_candidate)
		return 0;
	PmuxCoarseIndex index(module);
	int changes = simplify_congruent_modulo(index);
	changes += simplify_extremum_choices(index);
	changes += rewrite_excluded_sum(index, external_inputs);
	changes += share_common_arithmetic(index, external_inputs);
	return changes;
}

// 注册围绕选择器的算术优化 Pass。
struct OptPmuxArithPass : public Pass {
	// 注册 opt_pmux_arith 命令。
	OptPmuxArithPass() : Pass("opt_pmux_arith", "simplify and share modular arithmetic around selections") {}

	// 说明支持的算术化简和共享方式。
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

	// 查找被实例化的模块并在所选模块中运行算术优化。
	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		pool<IdString> instantiated;
		for (Module *module : design->modules())
			for (Cell *cell : module->cells())
				if (design->module(cell->type))
					instantiated.insert(cell->type);
		pmux_run_pass(design, "opt_pmux_arith", "Executing OPT_PMUX_ARITH pass.\n",
			      [&](Module *module) { return optimize_arithmetic_module(module, !instantiated.count(module->name)); });
	}
} OptPmuxArithPass;

PRIVATE_NAMESPACE_END

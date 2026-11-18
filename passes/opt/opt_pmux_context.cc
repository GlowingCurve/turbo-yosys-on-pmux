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

// 优化方法层的分支条件化简。根据已经选中的分支推导输入值，缩小或消除数据端的运算。

#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "passes/opt/pmux_rewrite.h"

#include <algorithm>
#include <optional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 筛选能够利用分支条件化简的数据单元。
bool can_specialize(Cell *cell)
{
	return cell->type.in(ID($mux), ID($pmux), ID($pos), ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($sub), ID($eq), ID($ne),
			     ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and), ID($logic_or), ID($reduce_and), ID($reduce_or),
			     ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
}

// 在一个选择器的各分支内推导约束并建立替换电路。
struct ContextRewrite {
	// 表示原始信号位或待生成节点的输出位。
	struct Bit {
		SigBit signal;
		std::optional<int> node = std::nullopt;
		int offset = 0;

		// 比较数据位的信号来源和位置。
		bool operator==(const Bit &) const = default;
		// 检查当前数据位是否为指定的常量。
		bool is(State state) const { return !node && signal == state; }
	};
	using Value = std::vector<Bit>;
	// 记录待生成单元的输入、输出位宽和原始属性来源。
	struct Node {
		Cell *original;
		std::vector<std::pair<IdString, Value>> inputs;
		int width;
		bool narrowed;
	};
	// 记录因分支约束而相等的信号位及其已知值。
	struct BitClass {
		SigBit parent;
		int rank = 0;
	};

	PmuxCoarseIndex index;
	Cell *consumer;
	dict<SigBit, BitClass> equalities;
	pool<std::pair<SigBit, SigBit>> direct_equalities;
	pool<SigBit> checked_assumptions;
	dict<Cell *, Value> cached;
	pool<Cell *> active, candidates;
	std::vector<Node> nodes;
	static constexpr int branch_budget = 16384;
	static constexpr int max_depth = 24;
	int budget = branch_budget;
	int truncated = 0;

	// 绑定选择器及其所在模块的连接索引。
	ContextRewrite(PmuxCoarseIndex &index, Cell *consumer) : index(index), consumer(consumer) {}

	// 检查信号位是否为确定的逻辑零或一。
	static bool binary(SigBit bit) { return bit == State::S0 || bit == State::S1; }

	// 把信号转换为可参与分支化简的数据位。
	static Value literal(const SigSpec &signal)
	{
		Value value;
		value.reserve(GetSize(signal));
		for (auto bit : signal)
			value.push_back({bit});
		return value;
	}

	// 检查化简结果是否与原信号逐位相同。
	static bool is_original(const Value &value, const SigSpec &signal)
	{
		log_assert(GetSize(value) == GetSize(signal));
		for (int i = 0; i < GetSize(value); i++)
			if (value[i].node || value[i].signal != signal[i])
				return false;
		return true;
	}

	// 查找等价信号位的代表。
	SigBit representative(SigBit bit)
	{
		auto entry = equalities.find(bit);
		if (entry == equalities.end() || entry->second.parent == bit)
			return bit;
		return entry->second.parent = representative(entry->second.parent);
	}

	// 在当前分支约束下读取信号的已知值。
	SigBit assumed(SigBit bit)
	{
		auto root = representative(bit);
		return binary(root) ? root : bit;
	}

	// 合并相等约束并检测已知常量之间的矛盾。
	bool equate(SigBit left, SigBit right)
	{
		left = representative(left);
		right = representative(right);
		if (!left.wire && !right.wire)
			return binary(left) && left == right;
		if (left == right)
			return true;
		if (!left.wire)
			std::swap(left, right);
		if (!right.wire) {
			if (!binary(right))
				return false;
			equalities[left] = {right};
			return true;
		}
		equalities.insert({left, {left}});
		equalities.insert({right, {right}});
		if (equalities.at(left).rank < equalities.at(right).rank)
			std::swap(left, right);
		auto &parent = equalities.at(left);
		auto &child = equalities.at(right);
		if (parent.rank == child.rank)
			parent.rank++;
		child.parent = left;
		return true;
	}

	// 以固定顺序记录一对信号，便于查找相等关系。
	static std::pair<SigBit, SigBit> ordered_pair(SigBit left, SigBit right)
	{
		if (right < left)
			std::swap(left, right);
		return {left, right};
	}

	// 把两个数据位相等的条件传播到它们的来源。
	bool assume_equal(SigBit left, SigBit right, int depth)
	{
		if (consumer->type == ID($mux)) {
			// 选择信号未定义时，$mux 仍可保留两个分支中相同的已定义位。
			// 中间位未定义时，两个直接相等条件无法约束两端的已定义值相等。
			if (left.wire && right.wire) {
				direct_equalities.insert(ordered_pair(left, right));
				return true;
			}
			if (binary(left))
				return assume(right, left.data, depth);
			return binary(right) && assume(left, right.data, depth);
		}
		if (!equate(left, right))
			return false;
		auto value = assumed(left);
		return !binary(value) || (assume(left, value.data, depth) && assume(right, value.data, depth));
	}

	// 利用不相等比较中唯一可能不同的数据位推导约束。
	bool assume_unequal(const SigSpec &a, const SigSpec &b, int depth)
	{
		log_assert(GetSize(a) == GetSize(b) && budget >= 0);
		if (GetSize(a) > budget)
			return true;
		budget -= GetSize(a);
		bool merges_unknown = consumer->type == ID($mux);
		std::optional<std::pair<SigBit, State>> mismatch;
		for (int i = 0; i < GetSize(a); ++i) {
			auto left = a[i], right = b[i];
			if (!merges_unknown) {
				left = representative(left);
				right = representative(right);
			}
			if ((!left.wire && !binary(left)) || (!right.wire && !binary(right)))
				return true;
			// 相同导线也可能使比较结果为 X，普通 $mux 仍会合并两路数据。
			if (left == right && (!merges_unknown || binary(left)))
				continue;
			if (!left.wire)
				std::swap(left, right);
			if (!left.wire || !binary(right))
				return true;
			auto required = std::make_pair(left, right == State::S0 ? State::S1 : State::S0);
			if (mismatch && *mismatch != required)
				return true;
			mismatch = required;
		}
		return !mismatch || assume(mismatch->first, mismatch->second, depth + 1);
	}

	// 按选择器类型读取可安全参与条件推导的操作数。
	SigBit implication_operand(SigBit bit)
	{
		// 对 $mux，组合分支事实不能证明选择信号为 X 时某个操作数仍是常量。
		return consumer->type == ID($mux) ? bit : assumed(bit);
	}

	// 根据归约结果反推可确定的输入。
	bool assume_reduction(const SigSpec &inputs, bool conjunction, bool required, int depth)
	{
		State value = required ? State::S1 : State::S0;
		if (required == conjunction) {
			for (auto input : inputs) {
				if (budget <= 0)
					break;
				if (!assume(input, value, depth + 1))
					return false;
			}
			return true;
		}

		if (GetSize(inputs) > budget)
			return true;
		budget -= GetSize(inputs);
		std::optional<SigBit> remaining;
		for (auto input : inputs) {
			SigBit known = implication_operand(input);
			if (known == value)
				return true;
			if (binary(known))
				continue;
			if (remaining && *remaining != input)
				return true;
			remaining = input;
		}
		return remaining && assume(*remaining, value, depth + 1);
	}

	// 由奇偶校验结果推断唯一未知的输入位。
	bool assume_parity(const SigSpec &inputs, bool required, int depth)
	{
		if (GetSize(inputs) > budget)
			return true;
		budget -= GetSize(inputs);
		SigSpec remaining;
		for (auto input : inputs) {
			SigBit known = implication_operand(input);
			if (binary(known))
				required ^= known == State::S1;
			else if (!known.wire)
				return false;
			else if (GetSize(remaining) == 2)
				return true;
			else
				remaining.append(input);
		}
		if (remaining.empty())
			return !required;
		if (GetSize(remaining) == 1)
			return assume(remaining[0], required ? State::S1 : State::S0, depth + 1);
		return required || assume_equal(remaining[0], remaining[1], depth + 1);
	}

	// 从逻辑与或逻辑或的结果推导操作数条件。
	bool assume_logical(Cell *cell, bool required, int depth)
	{
		auto a = index.port(cell, ID::A);
		auto b = index.port(cell, ID::B);
		if (GetSize(a) + GetSize(b) > budget)
			return true;
		if (cell->type == ID($logic_or)) {
			a.append(b);
			return assume_reduction(a, false, required, depth);
		}
		if (required)
			return assume_reduction(a, false, true, depth) && assume_reduction(b, false, true, depth);

		const SigSpec *operands[] = {&a, &b};
		for (int i = 0; i < 2; ++i)
			for (auto bit : *operands[i]) {
				if (budget <= 0)
					return true;
				--budget;
				if (implication_operand(bit) == State::S1)
					return assume_reduction(*operands[1 - i], false, false, depth);
			}
		return true;
	}

	// 记录分支所需的位值并在预算内追溯驱动。
	bool assume(SigBit bit, State value, int depth = 0)
	{
		log_assert(budget >= 0);
		if (budget == 0 || depth > max_depth)
			return true;
		budget--;
		if (!equate(bit, value))
			return false;
		if (!bit.wire || !checked_assumptions.insert(bit).second)
			return true;

		auto source = index.source(bit);
		if (!source || !source->cell || source->port != ID::Y || source->cell == consumer)
			return true;
		return assume_output(source->cell, source->offset, value == State::S1, depth);
	}

	// 从已知的单元输出反推约束，并保留当前递归预算。
	bool assume_output(Cell *cell, int offset, bool required, int depth)
	{
		auto type = cell->type;
		if (type == ID($not)) {
			auto a = index.port_bit(cell, ID::A, offset, pmux_cell_signed(cell));
			return assume(a, required ? State::S0 : State::S1, depth + 1);
		}
		if (type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
			bool sign = pmux_cell_signed(cell);
			SigSpec inputs({index.port_bit(cell, ID::A, offset, sign), index.port_bit(cell, ID::B, offset, sign)});
			if (type.in(ID($and), ID($or)))
				return assume_reduction(inputs, type == ID($and), required, depth);
			return assume_parity(inputs, required != (type == ID($xnor)), depth);
		}
		if (!type.in(ID($eq), ID($ne), ID($logic_not), ID($logic_and), ID($logic_or), ID($reduce_and), ID($reduce_or), ID($reduce_bool),
			     ID($reduce_xor), ID($reduce_xnor)))
			return true;
		if (offset != 0)
			return !required;

		if (type.in(ID($eq), ID($ne))) {
			auto comparison = pmux_comparison_operands(cell, budget, index.sigmap);
			if (!comparison)
				return true;
			const auto &[a, b] = *comparison;
			if ((type == ID($eq)) != required)
				return assume_unequal(a, b, depth);
			for (int i = 0; i < GetSize(a) && budget > 0; i++) {
				budget--;
				if (!assume_equal(a[i], b[i], depth + 1))
					return false;
			}
			return true;
		}
		if (type.in(ID($logic_and), ID($logic_or)))
			return assume_logical(cell, required, depth);
		auto input = index.port(cell, ID::A);
		if (type.in(ID($reduce_xor), ID($reduce_xnor)))
			return assume_parity(input, required != (type == ID($reduce_xnor)), depth);
		return assume_reduction(input, type == ID($reduce_and), required != (type == ID($logic_not)), depth);
	}

	// 检查一个数据向量中的位是否均为同一常量。
	static bool all_bits(const Value &value, State state)
	{
		return std::all_of(value.begin(), value.end(), [state](const Bit &bit) { return bit.is(state); });
	}

	// 在每个位均为常量时取得整个操作数的值。
	static std::optional<Const> constant(const Value &value)
	{
		Const::Builder bits(GetSize(value));
		for (const auto &bit : value) {
			if (!bit.is(State::S0) && !bit.is(State::S1))
				return std::nullopt;
			bits.push_back(bit.signal.data);
		}
		return bits.build();
	}

	// 按运算的符号规则补齐数据位宽。
	static void extend(Value &value, int width, bool sign)
	{
		Bit fill = sign && !value.empty() ? value.back() : Bit{State::S0};
		value.resize(width, fill);
	}

	// 检查两个表达式的位在当前条件下是否相同。
	bool equal(const Bit &left, const Bit &right)
	{
		if (left.node || right.node)
			return left == right;
		if ((!left.signal.wire && !binary(left.signal)) || (!right.signal.wire && !binary(right.signal)))
			return false;
		return representative(left.signal) == representative(right.signal) ||
		       direct_equalities.count(ordered_pair(left.signal, right.signal));
	}

	// 记录需要生成的运算节点并返回其输出位。
	Value make_node(Cell *cell, int width, Value a, Value b, Value s = {}, bool narrowed = false)
	{
		int node = GetSize(nodes);
		Node data{cell, {}, width, narrowed};
		data.inputs.emplace_back(ID::A, std::move(a));
		if (cell->hasPort(ID::B))
			data.inputs.emplace_back(ID::B, std::move(b));
		if (!s.empty())
			data.inputs.emplace_back(ID::S, std::move(s));
		nodes.push_back(std::move(data));
		Value result;
		result.reserve(width);
		for (int i = 0; i < width; i++)
			result.push_back({{}, node, i});
		return result;
	}

	// 去除大小比较中两个输入共有的常量高位。
	std::optional<Value> narrow_order(Cell *cell, Value a, Value b, int width)
	{
		bool sign = pmux_cell_signed(cell);
		int operands_width = std::max(GetSize(a), GetSize(b));
		extend(a, operands_width, sign);
		extend(b, operands_width, sign);
		int remaining = operands_width;
		while (remaining > 0) {
			const auto &left = a[remaining - 1], &right = b[remaining - 1];
			if ((!left.is(State::S0) || !right.is(State::S0)) && (!left.is(State::S1) || !right.is(State::S1)))
				break;
			remaining--;
		}
		if (remaining == 0 || remaining == operands_width)
			return std::nullopt;
		// 去掉相同的常量最高位后，剩余部分按无符号比较。
		a.resize(remaining);
		b.resize(remaining);
		return make_node(cell, width, std::move(a), std::move(b), {}, true);
	}

	// 按运算位宽扩展输入并利用相等位化简表达式。
	std::optional<Value> simplify_equal(Cell *cell, Value a, Value b, int width)
	{
		bool sign = pmux_cell_signed(cell);
		int operands_width = cell->type.in(ID($eq), ID($ne)) ? std::max(GetSize(a), GetSize(b)) : width;
		extend(a, operands_width, sign);
		extend(b, operands_width, sign);

		if (cell->type.in(ID($eq), ID($ne)))
			return simplify_eq_ne(cell, a, b, width);
		if (cell->type == ID($sub))
			return simplify_equal_sub(cell, a, b, width);
		return simplify_equal_xor(cell, a, b, width);
	}

	// 比较时跳过已经相等的位，只保留仍可能影响结果的输入。
	std::optional<Value> simplify_eq_ne(Cell *cell, const Value &a, const Value &b, int width)
	{
		int operands_width = GetSize(a);
		Value variable_a, variable_b;
		bool mismatch = false;
		for (int i = 0; i < operands_width; i++) {
			if (equal(a[i], b[i]))
				continue;
			if ((a[i].is(State::S0) && b[i].is(State::S1)) || (a[i].is(State::S1) && b[i].is(State::S0))) {
				mismatch = true;
				break;
			}
			variable_a.push_back(a[i]);
			variable_b.push_back(b[i]);
		}
		if (!mismatch) {
			if (GetSize(variable_a) == operands_width)
				return std::nullopt;
			if (!variable_a.empty())
				return make_node(cell, width, std::move(variable_a), std::move(variable_b), {}, true);
		}
		Value result(width, Bit{State::S0});
		result[0] = {(cell->type == ID($eq)) != mismatch ? State::S1 : State::S0};
		return result;
	}

	// 相同低位相减得到零，高位可单独计算。
	std::optional<Value> simplify_equal_sub(Cell *cell, const Value &a, const Value &b, int width)
	{
		int prefix = 0;
		while (prefix < width && equal(a[prefix], b[prefix]))
			prefix++;
		if (prefix == 0)
			return std::nullopt;
		Value result(prefix, Bit{State::S0});
		if (prefix < width) {
			// 相同低位相减无需向高位借位。
			Value high_a(a.begin() + prefix, a.end());
			Value high_b(b.begin() + prefix, b.end());
			auto high = make_node(cell, width - prefix, std::move(high_a), std::move(high_b), {}, true);
			result.insert(result.end(), high.begin(), high.end());
		}
		return result;
	}

	// 将异或结果中已知的位直接连接，仅对其余位生成运算单元。
	std::optional<Value> simplify_equal_xor(Cell *cell, const Value &a, const Value &b, int width)
	{
		log_assert(cell->type == ID($xor));
		Value result(width, Bit{State::S0});
		Value variable_a, variable_b;
		std::vector<int> variable_offsets;
		bool simplified = false;
		for (int i = 0; i < width; i++) {
			if (equal(a[i], b[i])) {
				simplified = true;
			} else if (a[i].is(State::S0)) {
				result[i] = b[i];
				simplified = true;
			} else if (b[i].is(State::S0)) {
				result[i] = a[i];
				simplified = true;
			} else {
				variable_a.push_back(a[i]);
				variable_b.push_back(b[i]);
				variable_offsets.push_back(i);
			}
		}
		if (!simplified)
			return std::nullopt;
		if (!variable_offsets.empty()) {
			auto variable = make_node(cell, GetSize(variable_offsets), std::move(variable_a), std::move(variable_b), {}, true);
			for (int i = 0; i < GetSize(variable_offsets); i++)
				result[variable_offsets[i]] = variable[i];
		}
		return result;
	}

	// 根据单元类型选择适用的分支化简规则。
	static std::optional<Value> simplify(Cell *cell, const Value &a, const Value &b, const Value &s, int width)
	{
		if (cell->type.in(ID($mux), ID($pmux)))
			return simplify_selector(cell, a, b, s, width);
		auto left = constant(a);
		if (left) {
			auto right = constant(b);
			if (right)
				return literal(CellTypes::eval(cell, *left, *right));
		}
		if (cell->type.in(ID($and), ID($or), ID($xnor)))
			return simplify_bitwise(cell, a, b, width);
		return simplify_identity(cell, a, b, width);
	}

	// $mux 的两个输入相同时可忽略未知选择位。$pmux 需要确定唯一选中的分支。
	static std::optional<Value> simplify_selector(Cell *cell, const Value &a, const Value &b, const Value &s, int width)
	{
		if (cell->type == ID($mux)) {
			if (s[0].is(State::S0) || a == b)
				return a;
			if (s[0].is(State::S1))
				return b;
			return std::nullopt;
		}
		if (cell->type == ID($pmux)) {
			std::optional<int> selected;
			for (int i = 0; i < GetSize(s); i++) {
				if (s[i].is(State::S0))
					continue;
				if (selected || !s[i].is(State::S1))
					return std::nullopt;
				selected = i;
			}
			if (!selected)
				return a;
			return Value(b.begin() + *selected * width, b.begin() + (*selected + 1) * width);
		}
		return std::nullopt;
	}

	// 利用逻辑运算的控制值和加减零恒等式直接连接结果。
	static std::optional<Value> simplify_identity(Cell *cell, const Value &a, const Value &b, int width)
	{
		if (cell->type.in(ID($logic_and), ID($logic_or))) {
			auto logical_value = [](const Value &value) {
				if (std::any_of(value.begin(), value.end(), [](const Bit &bit) { return bit.is(State::S1); }))
					return State::S1;
				return all_bits(value, State::S0) ? State::S0 : State::Sx;
			};
			State left = logical_value(a);
			State right = logical_value(b);
			State controlling = cell->type == ID($logic_and) ? State::S0 : State::S1;
			if (left == controlling || right == controlling || (left != State::Sx && left == right)) {
				Value result(width, Bit{State::S0});
				result[0] = {left == controlling || right == controlling ? controlling : left};
				return result;
			}
		}

		bool sign = pmux_cell_signed(cell);
		bool zero_left_add = cell->type == ID($add) && all_bits(a, State::S0);
		if (cell->type == ID($pos) || zero_left_add || (cell->type.in(ID($add), ID($sub)) && all_bits(b, State::S0))) {
			Value result = zero_left_add ? b : a;
			extend(result, width, sign);
			return result;
		}
		return std::nullopt;
	}

	// 分别检查每个输出位是否能用常量或某个输入替代。
	static std::optional<Value> simplify_bitwise(Cell *cell, const Value &a, const Value &b, int width)
	{
		bool sign = pmux_cell_signed(cell);
		Value left = a, right = b;
		extend(left, width, sign);
		extend(right, width, sign);
		Value result;
		for (int i = 0; i < width; i++) {
			auto x = left[i], y = right[i];
			if (cell->type == ID($and) && (x.is(State::S0) || y.is(State::S0)))
				result.push_back({State::S0});
			else if (cell->type == ID($or) && (x.is(State::S1) || y.is(State::S1)))
				result.push_back({State::S1});
			else if ((cell->type == ID($and) && x.is(State::S1)) || (cell->type == ID($or) && x.is(State::S0)) ||
				 (cell->type == ID($xnor) && x.is(State::S1)))
				result.push_back(y);
			else if ((cell->type == ID($and) && y.is(State::S1)) || (cell->type == ID($or) && y.is(State::S0)) ||
				 (cell->type == ID($xnor) && y.is(State::S1)))
				result.push_back(x);
			else
				return std::nullopt;
		}
		return result;
	}

	// 递归替换信号各位并保留访问预算。
	Value specialize(const SigSpec &signal, int depth = 0)
	{
		if (depth > max_depth || GetSize(signal) > budget) {
			++truncated;
			return literal(signal);
		}
		budget -= GetSize(signal);
		Value result;
		result.reserve(GetSize(signal));
		for (auto original : signal) {
			auto bit = assumed(original);
			if (bit != original) {
				result.push_back({bit});
				continue;
			}
			auto source = index.source(bit);
			if (!source || source->port != ID::Y || source->cell == consumer) {
				result.push_back({bit});
				continue;
			}
			auto cell = source->cell;
			auto found = cached.find(cell);
			if (found != cached.end()) {
				result.push_back(found->second[source->offset]);
				continue;
			}
			if (can_specialize(cell) && index.editable(cell)) {
				if (depth >= max_depth || GetSize(cell->getPort(ID::Y)) > budget) {
					++truncated;
				} else if (active.insert(cell).second) {
					const int completed = truncated;
					candidates.insert(cell);
					auto value = specialize(cell, depth + 1);
					active.erase(cell);
					result.push_back(value[source->offset]);
					if (truncated == completed)
						cached.emplace(cell, std::move(value));
					continue;
				}
			}
			result.push_back({bit});
		}
		return result;
	}

	// 利用已知输入化简驱动单元并缓存结果。
	Value specialize(Cell *cell, int depth)
	{
		auto original_a = index.port(cell, ID::A);
		auto original_b = cell->hasPort(ID::B) ? index.port(cell, ID::B) : SigSpec();
		auto original_s = pmux_has_selection_port(cell, ID::S) ? index.port(cell, ID::S) : SigSpec();
		auto output = index.port(cell, ID::Y);
		auto a = specialize(original_a, depth);
		auto b = specialize(original_b, depth);
		auto s = specialize(original_s, depth);
		bool unchanged = is_original(a, original_a) && is_original(b, original_b) && is_original(s, original_s);
		if (!unchanged) {
			auto simplified = simplify(cell, a, b, s, GetSize(output));
			if (simplified)
				return std::move(*simplified);
		}
		if (!unchanged && cell->type.in(ID($lt), ID($le), ID($gt), ID($ge))) {
			auto narrowed = narrow_order(cell, a, b, GetSize(output));
			if (narrowed)
				return std::move(*narrowed);
		}
		if (cell->type.in(ID($xor), ID($sub), ID($eq), ID($ne))) {
			auto simplified = simplify_equal(cell, a, b, GetSize(output));
			if (simplified)
				return std::move(*simplified);
		}
		if (unchanged)
			return literal(output);
		return make_node(cell, GetSize(output), std::move(a), std::move(b), std::move(s));
	}

	// 建立当前分支的条件，取得相应的数据表达式。
	Value branch(const SigSpec &data, const SigSpec &select, std::optional<int> selected)
	{
		budget = branch_budget;
		truncated = 0;
		equalities.clear();
		direct_equalities.clear();
		checked_assumptions.clear();
		cached.clear();
		if (!selected) {
			for (auto bit : select)
				if (!assume(bit, State::S0))
					return literal(data);
		} else if (!assume(select[*selected], State::S1))
			return literal(data);
		return equalities.empty() ? literal(data) : specialize(data);
	}

	// 递归收集新表达式使用的外部输入和节点。
	void find_inputs(const Value &value, pool<SigBit> &inputs, pool<int> &needed)
	{
		for (const auto &bit : value) {
			if (!bit.node) {
				if (bit.signal.wire)
					inputs.insert(bit.signal);
			} else if (needed.insert(*bit.node).second) {
				for (const auto &port : nodes[*bit.node].inputs)
					find_inputs(port.second, inputs, needed);
			}
		}
	}

	// 用暂存连线替换表达式中记录的节点编号。
	static SigSpec materialize(const Value &value, const std::vector<Wire *> &wires)
	{
		SigSpec result;
		for (const auto &bit : value)
			result.append(bit.node ? SigBit(wires[*bit.node], bit.offset) : bit.signal);
		return result;
	}

	// 构造仍需保留的分支运算，并把选择器接到新数据。
	void emit_nodes(PmuxRewrite &rewrite, const pool<int> &needed, const Value &a, const Value &b)
	{
		std::vector<Wire *> wires(nodes.size(), nullptr);
		for (int i = 0; i < GetSize(nodes); i++) {
			if (!needed.count(i))
				continue;
			const auto &node = nodes[i];
			wires[i] = rewrite.staging.addWire(NEW_ID, node.width);
			auto replacement = rewrite.clone_cell(NEW_ID, node.original);
			replacement->setPort(ID::Y, wires[i]);
			if (node.narrowed)
				replacement->setParam(ID::Y_WIDTH, node.width);
			for (const auto &[port, value] : node.inputs) {
				if (node.narrowed) {
					log_assert(port.in(ID::A, ID::B));
					replacement->setParam(port == ID::A ? ID::A_SIGNED : ID::B_SIGNED, false);
					replacement->setParam(port == ID::A ? ID::A_WIDTH : ID::B_WIDTH, GetSize(value));
				}
				replacement->setPort(port, materialize(value, wires));
			}
		}
		auto selection = rewrite.clone_cell(consumer->name, consumer);
		selection->setPort(ID::A, materialize(a, wires));
		selection->setPort(ID::B, materialize(b, wires));
	}

	// 收集分支化简结果并提交可替换的电路。
	bool run()
	{
		auto select = index.port(consumer, ID::S);
		auto original_a = index.port(consumer, ID::A);
		auto original_b = index.port(consumer, ID::B);
		if (GetSize(original_a) + GetSize(original_b) + GetSize(select) > branch_budget)
			return false;
		auto a = branch(original_a, select, std::nullopt);
		Value b;
		for (int i = 0; i < GetSize(select); i++) {
			auto row = branch(original_b.extract(i * GetSize(original_a), GetSize(original_a)), select, i);
			b.insert(b.end(), row.begin(), row.end());
		}
		if (is_original(a, original_a) && is_original(b, original_b))
			return false;
		pool<SigBit> retained;
		pool<int> needed;
		find_inputs(a, retained, needed);
		find_inputs(b, retained, needed);
		for (auto bit : select)
			if (bit.wire)
				retained.insert(bit);
		pool<SigBit> outputs;
		for (auto bit : index.port(consumer, ID::Y))
			outputs.insert(bit);
		candidates.insert(consumer);

		PmuxRewrite rewrite(index.module, index, "context");
		rewrite.find_removable(candidates, {}, outputs, retained);
		if (!rewrite.removed.count(consumer) ||
		    std::any_of(needed.begin(), needed.end(), [&](int i) { return !rewrite.removed.count(nodes[i].original); }))
			return false;

		emit_nodes(rewrite, needed, a, b);
		if (!rewrite.validate())
			return false;
		rewrite.commit();
		return true;
	}
};

// 在模块内逐个检查允许改写的选择器。
int specialize_branch_context(PmuxCoarseIndex &index)
{
	auto module = index.module;
	std::vector<IdString> selections;
	for (auto cell : module->selected_cells())
		if (pmux_has_selection_port(cell, ID::S))
			selections.push_back(cell->name);
	if (selections.empty())
		return 0;

	int changes = 0;
	for (auto name : selections) {
		auto cell = module->cell(name);
		if (cell && pmux_has_selection_port(cell, ID::S) && index.editable(cell))
			changes += ContextRewrite(index, cell).run();
	}
	return changes;
}

// 注册基于分支条件的数据化简 Pass。
struct OptPmuxContextPass : public Pass {
	// 注册 opt_pmux_context 命令。
	OptPmuxContextPass() : Pass("opt_pmux_context", "simplify RTLIL data logic under mux branch conditions") {}

	// 说明分支条件传播及未知值保护条件。
	void help() override
	{
		log("    opt_pmux_context [selection]\n");
		log("\n");
		log("Propagate branch conditions into the data of $mux and $pmux cells.\n");
		log("Use constant bits and operand equalities implied by the conditions.\n");
		log("Rebuild an operation only when its original cell can be removed.\n");
		log("Rewrites can refine undefined values. Designs with case equality or tri-state drivers are skipped.\n");
		log("\n");
	}

	// 为所选模块建立共享索引并执行条件化简。
	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		pmux_run_pass(design, "opt_pmux_context", "Executing OPT_PMUX_CONTEXT pass (conditional RTLIL simplification).\n",
			      [](Module *module) {
				      PmuxCoarseIndex index(module);
				      return specialize_branch_context(index);
			      });
	}
} OptPmuxContextPass;

PRIVATE_NAMESPACE_END

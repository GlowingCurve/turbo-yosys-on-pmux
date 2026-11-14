#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "passes/opt/pmux_rewrite.h"

#include <algorithm>
#include <optional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool can_specialize(Cell *cell)
{
	return cell->type.in(ID($mux), ID($pmux), ID($pos), ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($sub),
			ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and), ID($logic_or),
			ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
}

struct ContextRewrite
{
	struct Bit {
		SigBit signal;
		std::optional<int> node = std::nullopt;
		int offset = 0;

		bool operator==(const Bit &) const = default;
		bool is(State state) const { return !node && signal == state; }
	};
	using Value = std::vector<Bit>;
	struct Node {
		Cell *original;
		std::vector<std::pair<IdString, Value>> inputs;
		int width;
		bool narrowed;
	};
	struct BitClass {
		SigBit parent;
		int rank = 0;
	};

	PmuxCoarseIndex &index;
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

	ContextRewrite(PmuxCoarseIndex &index, Cell *consumer) : index(index), consumer(consumer) {}

	static bool binary(SigBit bit)
	{
		return bit == State::S0 || bit == State::S1;
	}

	static Value literal(const SigSpec &signal)
	{
		Value value;
		value.reserve(GetSize(signal));
		for (auto bit : signal)
			value.push_back({bit});
		return value;
	}

	static bool is_original(const Value &value, const SigSpec &signal)
	{
		log_assert(GetSize(value) == GetSize(signal));
		for (int i = 0; i < GetSize(value); i++)
			if (value[i].node || value[i].signal != signal[i])
				return false;
		return true;
	}

	SigBit representative(SigBit bit)
	{
		auto entry = equalities.find(bit);
		if (entry == equalities.end() || entry->second.parent == bit)
			return bit;
		return entry->second.parent = representative(entry->second.parent);
	}

	SigBit assumed(SigBit bit)
	{
		auto root = representative(bit);
		return binary(root) ? root : bit;
	}

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

	static std::pair<SigBit, SigBit> ordered_pair(SigBit left, SigBit right)
	{
		if (right < left)
			std::swap(left, right);
		return {left, right};
	}

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

	SigBit implication_operand(SigBit bit)
	{
		// 对 $mux，组合分支事实不能证明选择信号为 X 时某个操作数仍是常量。
		return consumer->type == ID($mux) ? bit : assumed(bit);
	}

	SigBit operand_bit(Cell *cell, IdString port, int offset, bool sign) const
	{
		const auto &operand = cell->getPort(port);
		if (offset < GetSize(operand))
			return index.sigmap(operand[offset]);
		return sign && !operand.empty() ? index.sigmap(operand[GetSize(operand) - 1]) : SigBit(State::S0);
	}

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

	bool assume_logical(Cell *cell, bool required, int depth)
	{
		auto a = index.port(cell, ID::A), b = index.port(cell, ID::B);
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
		auto cell = source->cell;
		auto type = cell->type;
		bool required = value == State::S1;
		if (type == ID($not)) {
			auto a = operand_bit(cell, ID::A, source->offset, pmux_is_signed_port(cell, ID::A));
			return assume(a, required ? State::S0 : State::S1, depth + 1);
		}
		if (type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
			bool sign = pmux_is_signed_port(cell, ID::A) && pmux_is_signed_port(cell, ID::B);
			SigSpec inputs({operand_bit(cell, ID::A, source->offset, sign), operand_bit(cell, ID::B, source->offset, sign)});
			if (type.in(ID($and), ID($or)))
				return assume_reduction(inputs, type == ID($and), required, depth);
			return assume_parity(inputs, required != (type == ID($xnor)), depth);
		}
		if (!type.in(ID($eq), ID($ne), ID($logic_not), ID($logic_and), ID($logic_or), ID($reduce_and), ID($reduce_or),
				ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor)))
			return true;
		if (source->offset != 0)
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

	static bool all_bits(const Value &value, State state)
	{
		return std::all_of(value.begin(), value.end(), [state](const Bit &bit) { return bit.is(state); });
	}

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

	static void extend(Value &value, int width, bool sign)
	{
		Bit fill = sign && !value.empty() ? value.back() : Bit{State::S0};
		value.resize(width, fill);
	}

	bool equal(const Bit &left, const Bit &right)
	{
		if (left.node || right.node)
			return left == right;
		if ((!left.signal.wire && !binary(left.signal)) || (!right.signal.wire && !binary(right.signal)))
			return false;
		return representative(left.signal) == representative(right.signal) ||
			direct_equalities.count(ordered_pair(left.signal, right.signal));
	}

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

	std::optional<Value> narrow_order(Cell *cell, Value a, Value b, int width)
	{
		bool sign = pmux_is_signed_port(cell, ID::A) && pmux_is_signed_port(cell, ID::B);
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

	std::optional<Value> simplify_equal(Cell *cell, Value a, Value b, int width)
	{
		bool sign = pmux_is_signed_port(cell, ID::A) && pmux_is_signed_port(cell, ID::B);
		int operands_width = cell->type.in(ID($eq), ID($ne)) ? std::max(GetSize(a), GetSize(b)) : width;
		extend(a, operands_width, sign);
		extend(b, operands_width, sign);

		if (cell->type.in(ID($eq), ID($ne))) {
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

		if (cell->type == ID($sub)) {
			int prefix = 0;
			while (prefix < width && equal(a[prefix], b[prefix]))
				prefix++;
			if (prefix == 0)
				return std::nullopt;
			Value result(prefix, Bit{State::S0});
			if (prefix < width) {
				// 相同低位相减无需向高位借位。
				Value high_a(a.begin() + prefix, a.end()), high_b(b.begin() + prefix, b.end());
				auto high = make_node(cell, width - prefix, std::move(high_a), std::move(high_b), {}, true);
				result.insert(result.end(), high.begin(), high.end());
			}
			return result;
		}

		log_assert(cell->type == ID($xor));
		Value result(width, Bit{State::S0}), variable_a, variable_b;
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

	static std::optional<Value> simplify(Cell *cell, const Value &a, const Value &b, const Value &s, int width)
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
		if (auto left = constant(a))
			if (auto right = constant(b))
				return literal(CellTypes::eval(cell, *left, *right));
		if (cell->type.in(ID($logic_and), ID($logic_or))) {
			auto logical_value = [](const Value &value) {
				if (std::any_of(value.begin(), value.end(), [](const Bit &bit) { return bit.is(State::S1); }))
					return State::S1;
				return all_bits(value, State::S0) ? State::S0 : State::Sx;
			};
			State left = logical_value(a), right = logical_value(b);
			State controlling = cell->type == ID($logic_and) ? State::S0 : State::S1;
			if (left == controlling || right == controlling || (left != State::Sx && left == right)) {
				Value result(width, Bit{State::S0});
				result[0] = {left == controlling || right == controlling ? controlling : left};
				return result;
			}
		}

		bool sign = pmux_is_signed_port(cell, ID::A) && (!cell->hasPort(ID::B) || pmux_is_signed_port(cell, ID::B));
		bool zero_left_add = cell->type == ID($add) && all_bits(a, State::S0);
		if (cell->type == ID($pos) || zero_left_add || (cell->type.in(ID($add), ID($sub)) && all_bits(b, State::S0))) {
			Value result = zero_left_add ? b : a;
			extend(result, width, sign);
			return result;
		}
		if (cell->type.in(ID($and), ID($or), ID($xnor))) {
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
				else if ((cell->type == ID($and) && x.is(State::S1)) ||
						 (cell->type == ID($or) && x.is(State::S0)) ||
						 (cell->type == ID($xnor) && x.is(State::S1)))
					result.push_back(y);
				else if ((cell->type == ID($and) && y.is(State::S1)) ||
						 (cell->type == ID($or) && y.is(State::S0)) ||
						 (cell->type == ID($xnor) && y.is(State::S1)))
					result.push_back(x);
				else
					return std::nullopt;
			}
			return result;
		}
		return std::nullopt;
	}

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

	Value specialize(Cell *cell, int depth)
	{
		auto original_a = index.port(cell, ID::A);
		auto original_b = cell->hasPort(ID::B) ? index.port(cell, ID::B) : SigSpec();
		auto original_s = pmux_has_selection_port(cell, ID::S) ? index.port(cell, ID::S) : SigSpec();
		auto output = index.port(cell, ID::Y);
		auto a = specialize(original_a, depth), b = specialize(original_b, depth), s = specialize(original_s, depth);
		bool unchanged = is_original(a, original_a) && is_original(b, original_b) && is_original(s, original_s);
		if (!unchanged)
			if (auto simplified = simplify(cell, a, b, s, GetSize(output)))
				return std::move(*simplified);
		if (!unchanged && cell->type.in(ID($lt), ID($le), ID($gt), ID($ge)))
			if (auto narrowed = narrow_order(cell, a, b, GetSize(output)))
				return std::move(*narrowed);
		if (cell->type.in(ID($xor), ID($sub), ID($eq), ID($ne)))
			if (auto simplified = simplify_equal(cell, a, b, GetSize(output)))
				return std::move(*simplified);
		if (unchanged)
			return literal(output);
		return make_node(cell, GetSize(output), std::move(a), std::move(b), std::move(s));
	}

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

	static SigSpec materialize(const Value &value, const std::vector<Wire *> &wires)
	{
		SigSpec result;
		for (const auto &bit : value)
			result.append(bit.node ? SigBit(wires[*bit.node], bit.offset) : bit.signal);
		return result;
	}

	bool run()
	{
		auto select = index.port(consumer, ID::S);
		auto original_a = index.port(consumer, ID::A), original_b = index.port(consumer, ID::B);
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
		if (!rewrite.removed.count(consumer) || std::any_of(needed.begin(), needed.end(), [&](int i) {
			return !rewrite.removed.count(nodes[i].original);
		}))
			return false;

		std::vector<Wire *> wires(nodes.size(), nullptr);
		for (int i = 0; i < GetSize(nodes); i++) {
			if (!needed.count(i))
				continue;
			const auto &node = nodes[i];
			wires[i] = rewrite.staging.addWire(NEW_ID, node.width);
			auto replacement = rewrite.staging.addCell(NEW_ID, node.original->type);
			replacement->attributes = node.original->attributes;
			replacement->parameters = node.original->parameters;
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
		auto selection = rewrite.staging.addCell(consumer->name, consumer);
		selection->setPort(ID::A, materialize(a, wires));
		selection->setPort(ID::B, materialize(b, wires));
		if (!rewrite.validate())
			return false;
		rewrite.commit();
		return true;
	}
};

int specialize_branches(Module *module)
{
	std::vector<IdString> selections;
	for (auto cell : module->selected_cells())
		if (pmux_has_selection_port(cell, ID::S))
			selections.push_back(cell->name);
	if (selections.empty())
		return 0;

	PmuxCoarseIndex index(module);
	int changes = 0;
	for (auto name : selections) {
		auto cell = module->cell(name);
		if (cell && pmux_has_selection_port(cell, ID::S) && index.editable(cell))
			changes += ContextRewrite(index, cell).run();
	}
	return changes;
}

struct OptPmuxContextPass : public Pass
{
	OptPmuxContextPass() : Pass("opt_pmux_context", "simplify RTLIL data logic under mux branch conditions") {}

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

	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		pmux_run_pass(design, "opt_pmux_context", "Executing OPT_PMUX_CONTEXT pass (conditional RTLIL simplification).\n",
				specialize_branches);
	}
} OptPmuxContextPass;

PRIVATE_NAMESPACE_END

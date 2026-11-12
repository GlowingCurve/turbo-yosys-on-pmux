#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "passes/opt/pmux_rewrite.h"

#include <algorithm>
#include <optional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool is_selection(Cell *cell)
{
	return cell->type.in(ID($mux), ID($pmux));
}

bool can_specialize(Cell *cell)
{
	return cell->type.in(ID($mux), ID($pmux), ID($pos), ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($add), ID($sub),
			ID($eq), ID($ne), ID($logic_not), ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
}

bool binary(SigBit bit)
{
	return bit == State::S0 || bit == State::S1;
}

bool signed_port(Cell *cell, IdString param)
{
	return cell->hasParam(param) && cell->getParam(param).as_bool();
}

struct ContextRewrite
{
	struct Bit {
		SigBit signal;
		int node = -1;
		int offset = 0;

		bool operator==(const Bit &) const = default;
		bool is(State state) const { return node < 0 && signal == state; }
	};
	using Value = std::vector<Bit>;
	struct Node {
		Cell *original;
		Value a, b, s;
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
	int budget = 16384;
	static constexpr int max_depth = 24;

	ContextRewrite(PmuxCoarseIndex &index, Cell *consumer) : index(index), consumer(consumer) {}

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
			if (value[i].node >= 0 || value[i].signal != signal[i])
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

	bool assume(SigBit bit, State value, int depth = 0)
	{
		if (budget <= 0 || depth > max_depth)
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
		if (!cell->type.in(ID($not), ID($eq), ID($ne), ID($logic_not), ID($reduce_and), ID($reduce_or), ID($reduce_bool)))
			return true;

		if (cell->type == ID($not)) {
			auto a = index.port(cell, ID::A);
			a.extend_u0(source->offset + 1, signed_port(cell, ID::A_SIGNED));
			return assume(a[source->offset], value == State::S1 ? State::S0 : State::S1, depth + 1);
		}
		if (source->offset != 0)
			return value == State::S0;

		if (cell->type.in(ID($eq), ID($ne))) {
			if ((cell->type == ID($eq)) != (value == State::S1))
				return true;
			auto comparison = index.comparison_operands(cell, budget);
			if (!comparison)
				return true;
			const auto &[a, b] = *comparison;
			for (int i = 0; i < GetSize(a) && budget > 0; i++) {
				budget--;
				if (!assume_equal(a[i], b[i], depth + 1))
					return false;
			}
			return true;
		}

		bool implies_all = cell->type.in(ID($logic_not), ID($reduce_and)) == (value == State::S1);
		State required = cell->type == ID($reduce_and) ? State::S1 : State::S0;
		if (implies_all)
			for (auto input : index.port(cell, ID::A)) {
				if (budget <= 0)
					break;
				if (!assume(input, required, depth + 1))
					return false;
			}
		return true;
	}

	static bool binary_constant(const Value &value)
	{
		return std::all_of(value.begin(), value.end(), [](const Bit &bit) { return bit.is(State::S0) || bit.is(State::S1); });
	}

	static bool zero(const Value &value)
	{
		return std::all_of(value.begin(), value.end(), [](const Bit &bit) { return bit.is(State::S0); });
	}

	static Const constant(const Value &value)
	{
		std::vector<State> bits;
		bits.reserve(value.size());
		for (const auto &bit : value)
			bits.push_back(bit.signal.data);
		return Const(std::move(bits));
	}

	static void extend(Value &value, int width, bool sign)
	{
		Bit fill = sign && !value.empty() ? value.back() : Bit{State::S0};
		value.resize(width, fill);
	}

	bool equal(const Bit &left, const Bit &right)
	{
		if (left.node >= 0 || right.node >= 0)
			return left == right;
		if ((!left.signal.wire && !binary(left.signal)) || (!right.signal.wire && !binary(right.signal)))
			return false;
		return representative(left.signal) == representative(right.signal) ||
			direct_equalities.count(ordered_pair(left.signal, right.signal));
	}

	Value make_node(Cell *cell, Value a, Value b, Value s, int width, bool narrowed = false)
	{
		int node = GetSize(nodes);
		nodes.push_back({cell, std::move(a), std::move(b), std::move(s), width, narrowed});
		Value result;
		result.reserve(width);
		for (int i = 0; i < width; i++)
			result.push_back({{}, node, i});
		return result;
	}

	std::optional<Value> simplify_equal(Cell *cell, Value a, Value b, int width)
	{
		bool sign = signed_port(cell, ID::A_SIGNED) && signed_port(cell, ID::B_SIGNED);
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
					return make_node(cell, std::move(variable_a), std::move(variable_b), {}, width, true);
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
				auto high = make_node(cell, std::move(high_a), std::move(high_b), {}, width - prefix, true);
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
			auto variable = make_node(cell, std::move(variable_a), std::move(variable_b), {}, GetSize(variable_offsets), true);
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
			if (!binary_constant(s))
				return std::nullopt;
			int selected = -1;
			for (int i = 0; i < GetSize(s); i++) {
				if (s[i].is(State::S0))
					continue;
				if (selected >= 0)
					return std::nullopt;
				selected = i;
			}
			if (selected < 0)
				return a;
			return Value(b.begin() + selected * width, b.begin() + (selected + 1) * width);
		}
		if (binary_constant(a) && binary_constant(b))
			return literal(CellTypes::eval(cell, constant(a), constant(b)));

		bool sign = signed_port(cell, ID::A_SIGNED) && (!cell->hasPort(ID::B) || signed_port(cell, ID::B_SIGNED));
		if (cell->type == ID($pos) || (cell->type.in(ID($add), ID($sub)) && zero(b))) {
			Value result = a;
			extend(result, width, sign);
			return result;
		}
		if (cell->type == ID($add) && zero(a)) {
			Value result = b;
			extend(result, width, sign);
			return result;
		}
		if (cell->type.in(ID($and), ID($or), ID($xor), ID($xnor))) {
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
						 (cell->type.in(ID($or), ID($xor)) && x.is(State::S0)) ||
						 (cell->type == ID($xnor) && x.is(State::S1)))
					result.push_back(y);
				else if ((cell->type == ID($and) && y.is(State::S1)) ||
						 (cell->type.in(ID($or), ID($xor)) && y.is(State::S0)) ||
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
		if (depth > max_depth || GetSize(signal) > budget)
			return literal(signal);
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
			if (!source || !source->cell || source->port != ID::Y || source->cell == consumer || budget <= 0) {
				result.push_back({bit});
				continue;
			}
			auto cell = source->cell;
			auto found = cached.find(cell);
			if (found == cached.end() && can_specialize(cell) && GetSize(cell->getPort(ID::Y)) <= budget &&
				index.editable(cell) && active.insert(cell).second) {
				candidates.insert(cell);
				auto value = specialize(cell, depth + 1);
				active.erase(cell);
				found = cached.insert(std::make_pair(cell, std::move(value))).first;
			}
			if (found == cached.end())
				result.push_back({bit});
			else
				result.push_back(found->second[source->offset]);
		}
		return result;
	}

	Value specialize(Cell *cell, int depth)
	{
		auto original_a = index.port(cell, ID::A);
		auto original_b = cell->hasPort(ID::B) ? index.port(cell, ID::B) : SigSpec();
		auto original_s = is_selection(cell) ? index.port(cell, ID::S) : SigSpec();
		auto output = index.port(cell, ID::Y);
		auto a = specialize(original_a, depth), b = specialize(original_b, depth), s = specialize(original_s, depth);
		bool unchanged = is_original(a, original_a) && is_original(b, original_b) && is_original(s, original_s);
		if (!unchanged)
			if (auto simplified = simplify(cell, a, b, s, GetSize(output)))
				return std::move(*simplified);
		if (cell->type.in(ID($xor), ID($sub), ID($eq), ID($ne)))
			if (auto simplified = simplify_equal(cell, a, b, GetSize(output)))
				return std::move(*simplified);
		if (unchanged)
			return literal(output);
		return make_node(cell, std::move(a), std::move(b), std::move(s), GetSize(output));
	}

	Value branch(const SigSpec &data, const SigSpec &select, int selected)
	{
		equalities.clear();
		direct_equalities.clear();
		checked_assumptions.clear();
		cached.clear();
		if (selected < 0) {
			for (auto bit : select)
				if (!assume(bit, State::S0))
					return literal(data);
		} else if (!assume(select[selected], State::S1))
			return literal(data);
		return equalities.empty() ? literal(data) : specialize(data);
	}

	void find_inputs(const Value &value, pool<SigBit> &inputs, pool<int> &needed)
	{
		for (const auto &bit : value) {
			if (bit.node < 0) {
				if (bit.signal.wire)
					inputs.insert(bit.signal);
			} else if (needed.insert(bit.node).second) {
				const auto &node = nodes[bit.node];
				find_inputs(node.a, inputs, needed);
				find_inputs(node.b, inputs, needed);
				find_inputs(node.s, inputs, needed);
			}
		}
	}

	static SigSpec materialize(const Value &value, const std::vector<Wire *> &wires)
	{
		SigSpec result;
		for (const auto &bit : value)
			result.append(bit.node < 0 ? bit.signal : SigBit(wires[bit.node], bit.offset));
		return result;
	}

	bool run()
	{
		auto select = index.port(consumer, ID::S);
		auto original_a = index.port(consumer, ID::A), original_b = index.port(consumer, ID::B);
		if (GetSize(original_a) + GetSize(original_b) + GetSize(select) > budget)
			return false;
		auto a = branch(original_a, select, -1);
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
		auto removed = index.removable(candidates, {}, outputs, retained);
		if (!removed.count(consumer) || std::any_of(needed.begin(), needed.end(), [&](int i) {
			return !removed.count(nodes[i].original);
		}))
			return false;

		PmuxRewrite rewrite(index.module, index, "context");
		rewrite.removed = std::move(removed);
		std::vector<Wire *> wires(nodes.size(), nullptr);
		for (int i = 0; i < GetSize(nodes); i++) {
			if (!needed.count(i))
				continue;
			const auto &node = nodes[i];
			wires[i] = rewrite.staging.addWire(NEW_ID, node.width);
			auto replacement = rewrite.staging.addCell(NEW_ID, node.original->type);
			replacement->attributes = node.original->attributes;
			replacement->parameters = node.original->parameters;
			if (node.narrowed) {
				replacement->setParam(ID::A_SIGNED, false);
				replacement->setParam(ID::B_SIGNED, false);
				replacement->setParam(ID::A_WIDTH, GetSize(node.a));
				replacement->setParam(ID::B_WIDTH, GetSize(node.b));
				replacement->setParam(ID::Y_WIDTH, node.width);
			}
			replacement->setPort(ID::Y, wires[i]);
			replacement->setPort(ID::A, materialize(node.a, wires));
			if (node.original->hasPort(ID::B))
				replacement->setPort(ID::B, materialize(node.b, wires));
			if (is_selection(replacement))
				replacement->setPort(ID::S, materialize(node.s, wires));
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
		log_header(design, "Executing OPT_PMUX_CONTEXT pass (conditional RTLIL simplification).\n");
		extra_args(args, 1, design);
		if (pmux_coarse_observes_undef(design))
			return;
		for (auto module : design->selected_modules()) {
			if (!module->processes.empty())
				continue;
			std::vector<IdString> selections;
			for (auto cell : module->selected_cells())
				if (is_selection(cell))
					selections.push_back(cell->name);
			if (selections.empty())
				continue;
			PmuxCoarseIndex index(module);
			int changes = 0;
			for (auto name : selections) {
				auto cell = module->cell(name);
				if (cell && index.editable(cell))
					changes += ContextRewrite(index, cell).run();
			}
			if (changes)
				log("Specialized %d selections in %s.\n", changes, log_id(module));
		}
	}
} OptPmuxContextPass;

PRIVATE_NAMESPACE_END

#include "kernel/celltypes.h"
#include "kernel/log.h"
#include "kernel/register.h"
#include "passes/opt/pmux_coarse.h"

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
	};

	PmuxCoarseIndex &index;
	Cell *consumer;
	dict<SigBit, State> facts;
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

	SigBit assumed(SigBit bit) const
	{
		auto fact = facts.find(bit);
		return fact == facts.end() ? bit : SigBit(fact->second);
	}

	bool assume(SigBit bit, State value, int depth = 0)
	{
		if (budget <= 0 || depth > max_depth)
			return true;
		budget--;
		if (!bit.wire)
			return bit == value;
		auto binding = facts.insert(std::make_pair(bit, value));
		if (!binding.second)
			return binding.first->second == value;

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
				auto left = assumed(a[i]), right = assumed(b[i]);
				if (binary(left) && !assume(right, left.data, depth + 1))
					return false;
				if (binary(right) && !assume(left, right.data, depth + 1))
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
		if (is_original(a, original_a) && is_original(b, original_b) && is_original(s, original_s))
			return literal(output);
		auto simplified = simplify(cell, a, b, s, GetSize(output));
		if (simplified)
			return std::move(*simplified);
		int node = GetSize(nodes);
		nodes.push_back({cell, std::move(a), std::move(b), std::move(s)});
		Value result;
		for (int i = 0; i < GetSize(output); i++)
			result.push_back({{}, node, i});
		return result;
	}

	Value branch(const SigSpec &data, const SigSpec &select, int selected)
	{
		facts.clear();
		cached.clear();
		if (selected < 0) {
			for (auto bit : select)
				if (!assume(bit, State::S0))
					return literal(data);
		} else if (!assume(select[selected], State::S1))
			return literal(data);
		return facts.empty() ? literal(data) : specialize(data);
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
		auto removed = index.removable(candidates, {consumer}, {}, retained);
		if (GetSize(removed) <= GetSize(needed))
			return false;
		pool<SigBit> outputs;
		for (auto bit : index.port(consumer, ID::Y))
			outputs.insert(bit);
		if (!index.independent(retained, outputs))
			return false;

		std::vector<Wire *> wires(nodes.size(), nullptr);
		for (int i = 0; i < GetSize(nodes); i++) {
			if (!needed.count(i))
				continue;
			const auto &node = nodes[i];
			wires[i] = index.module->addWire(NEW_ID, GetSize(node.original->getPort(ID::Y)));
			auto replacement = index.module->addCell(NEW_ID, node.original->type);
			replacement->attributes = node.original->attributes;
			replacement->parameters = node.original->parameters;
			replacement->setPort(ID::Y, wires[i]);
			replacement->setPort(ID::A, materialize(node.a, wires));
			if (node.original->hasPort(ID::B))
				replacement->setPort(ID::B, materialize(node.b, wires));
			if (is_selection(replacement))
				replacement->setPort(ID::S, materialize(node.s, wires));
		}
		consumer->setPort(ID::A, materialize(a, wires));
		consumer->setPort(ID::B, materialize(b, wires));
		for (auto cell : removed)
			index.module->remove(cell);
		log_debug("Specialized %s using %d fewer cells.\n", log_id(consumer), GetSize(removed) - GetSize(needed));
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
		log("Apply a rewrite when it reduces the number of RTLIL cells.\n");
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
			int before = module->cells_size();
			int changes = 0;
			for (auto name : selections) {
				auto cell = module->cell(name);
				if (cell && index.editable(cell))
					changes += ContextRewrite(index, cell).run();
			}
			if (changes)
				log("Specialized %d selections in %s, removing %d RTLIL cells net.\n", changes, log_id(module), before - module->cells_size());
		}
	}
} OptPmuxContextPass;

PRIVATE_NAMESPACE_END

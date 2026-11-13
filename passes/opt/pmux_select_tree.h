#ifndef YOSYS_PMUX_SELECT_TREE_H
#define YOSYS_PMUX_SELECT_TREE_H

#include "passes/opt/pmux_encoding.h"

#include <map>
#include <tuple>

YOSYS_NAMESPACE_BEGIN

class PmuxSelectTree
{
	enum class Op { literal, invert, bit_and, bit_or, bit_xor, bit_xnor, mux };
	struct Node {
		Op op;
		int a, b, select, stage;
		SigBit bit;
	};
	const PmuxCoarseIndex &index;
	const PmuxEncoding &encoding;
	std::vector<Node> nodes;
	dict<SigBit, int> literals;
	dict<std::tuple<int, Op, int, int, int>, int> operations;
	dict<std::pair<SigBit, int>, int> specialized;
	dict<int, bool> z_free;
	dict<int, std::optional<PmuxCoarseIndex::Port>> literal_inverters;
	pool<SigBit> active;
	int visits_left = 65536;

	int data_stage(int id) const { return id < 0 ? 0 : nodes[id].stage; }

	int operation(Op op, int a, int b = -1, int select = -1, int stage = 0)
	{
		if (op != Op::mux && op != Op::invert && b < a)
			std::swap(a, b);
		auto key = std::make_tuple(stage, op, a, b, select);
		auto previous = operations.find(key);
		if (previous != operations.end())
			return previous->second;
		int id = GetSize(nodes);
		nodes.push_back({op, a, b, select, stage, SigBit()});
		operations[key] = id;
		return id;
	}

	int gate(Op op, int a, int b = -1)
	{
		if (op == Op::invert) {
			if (constant(a, State::S0) || constant(a, State::S1))
				return literal(constant(a, State::S0) ? State::S1 : State::S0);
			if (nodes[a].op == Op::invert)
				return nodes[a].a;
		} else {
			if ((op == Op::bit_and && constant(b, State::S0)) || (op == Op::bit_or && constant(b, State::S1)))
				return b;
			if ((op == Op::bit_and && constant(a, State::S0)) || (op == Op::bit_or && constant(a, State::S1)))
				return a;
			if ((op == Op::bit_and && constant(b, State::S1)) || (op == Op::bit_or && constant(b, State::S0)))
				return a;
			if ((op == Op::bit_and && constant(a, State::S1)) || (op == Op::bit_or && constant(a, State::S0)))
				return b;
			if (op == Op::bit_xor || op == Op::bit_xnor) {
				if (constant(b, State::S0) || constant(b, State::S1))
					return constant(b, State::S1) == (op == Op::bit_xor) ? gate(Op::invert, a) : a;
				if (constant(a, State::S0) || constant(a, State::S1))
					return constant(a, State::S1) == (op == Op::bit_xor) ? gate(Op::invert, b) : b;
			}
		}
		return operation(op, a, b, -1, std::max(data_stage(a), data_stage(b)) + 1);
	}

	bool cannot_output_z(int id)
	{
		auto cached = z_free.find(id);
		if (cached != z_free.end())
			return cached->second;
		const auto &node = nodes[id];
		bool proven = true;
		if (node.op == Op::mux) {
			proven = cannot_output_z(node.a) && cannot_output_z(node.b);
		} else if (node.op == Op::literal) {
			if (node.bit.wire) {
				auto source = index.source(node.bit);
				proven = source && source->port == ID::Y &&
						source->cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($logic_not),
							ID($logic_and), ID($logic_or), ID($reduce_bool), ID($reduce_or), ID($reduce_and),
							ID($reduce_xor), ID($reduce_xnor), ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge));
			} else {
				proven = node.bit != State::Sz;
			}
		}
		z_free.emplace(id, proven);
		return proven;
	}

	bool complementary(int value, int inverse)
	{
		const auto &node = nodes[inverse];
		if (node.op == Op::invert)
			return node.a == value && cannot_output_z(value);
		if (node.op != Op::literal || !node.bit.wire || nodes[value].op != Op::literal)
			return false;
		auto cached = literal_inverters.find(inverse);
		if (cached == literal_inverters.end()) {
			auto source = index.source(node.bit);
			if (source && (source->port != ID::Y || source->cell->type != ID($not)))
				source.reset();
			cached = literal_inverters.emplace(inverse, source).first;
		}
		const auto &source = cached->second;
		if (!source || operand(source->cell, ID::A, source->offset, source->cell->getParam(ID::A_SIGNED).as_bool()) != nodes[value].bit ||
				!cannot_output_z(value))
			return false;
		producers.insert(source->cell);
		return true;
	}

	int mux(int a, int b, int select, int stage)
	{
		if (a == b || constant(select, State::S0))
			return a;
		if (constant(select, State::S1))
			return b;
		if (constant(a, State::S0) && constant(b, State::S1))
			return select;
		// 高阻态可通过 mux 原样输出，按位异或会将其转成未知值。
		if (complementary(a, b))
			return operation(Op::bit_xor, a, select, -1, stage);
		if (complementary(b, a))
			return operation(Op::bit_xnor, b, select, -1, stage);
		return operation(Op::mux, a, b, select, stage);
	}

	SigBit operand(Cell *cell, IdString port, int offset, bool sign) const
	{
		const auto &value = cell->getPort(port);
		if (offset < GetSize(value))
			return index.sigmap(value[offset]);
		return sign && !value.empty() ? index.sigmap(value[GetSize(value) - 1]) : SigBit(State::S0);
	}

	int specialize(SigBit bit, int code, int depth)
	{
		auto control = encoding.slots.find(bit);
		if (control != encoding.slots.end())
			return literal(code & (1 << control->second) ? State::S1 : State::S0);
		int original = literal(bit);
		if (!bit.wire || depth == 0 || visits_left == 0)
			return original;
		auto key = std::make_pair(bit, code);
		auto cached = specialized.find(key);
		if (cached != specialized.end())
			return cached->second;
		auto source = index.source(bit);
		if (!source || source->port != ID::Y || !active.insert(bit).second)
			return original;
		--visits_left;
		auto cell = source->cell;
		int offset = source->offset, result = original;
		if (cell->type == ID($mux) && pmux_select_shape(cell)) {
			SigBit sel = index.port(cell, ID::S)[0];
			int select = specialize(sel, code, depth - 1);
			SigBit a = operand(cell, ID::A, offset, false), b = operand(cell, ID::B, offset, false);
			if (constant(select, State::S0) || constant(select, State::S1))
				result = specialize(constant(select, State::S0) ? a : b, code, depth - 1);
			else {
				int left = specialize(a, code, depth - 1), right = specialize(b, code, depth - 1);
				if (left != literal(a) || right != literal(b) || select != literal(sel))
					result = mux(left, right, select, std::max({data_stage(left), data_stage(right), data_stage(select)}) + 1);
			}
		} else if (cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor))) {
			bool unary = cell->type == ID($not);
			bool sign = cell->getParam(ID::A_SIGNED).as_bool() && (unary || cell->getParam(ID::B_SIGNED).as_bool());
			SigBit a = operand(cell, ID::A, offset, sign);
			int left = specialize(a, code, depth - 1);
			if (unary) {
				if (left != literal(a))
					result = gate(Op::invert, left);
			} else {
				SigBit b = operand(cell, ID::B, offset, sign);
				int right = specialize(b, code, depth - 1);
				if (left != literal(a) || right != literal(b)) {
					Op op = cell->type == ID($and) ? Op::bit_and : cell->type == ID($or) ? Op::bit_or :
						cell->type == ID($xor) ? Op::bit_xor : Op::bit_xnor;
					result = gate(op, left, right);
				}
			}
		}
		active.erase(bit);
		specialized[key] = result;
		if (result != original)
			producers.insert(cell);
		return result;
	}

public:
	struct Analysis {
		std::vector<bool> live;
		std::vector<SigBit> literals;
		int mux_bits = 0, data_end = 0;
	};

	Analysis analyze(const std::vector<int> &roots) const
	{
		Analysis result;
		result.live.resize(nodes.size());
		std::vector<int> pending = roots;
		while (!pending.empty()) {
			int id = pending.back();
			pending.pop_back();
			if (result.live[id])
				continue;
			result.live[id] = true;
			const auto &node = nodes[id];
			result.mux_bits += node.op == Op::mux;
			result.data_end = std::max(result.data_end, node.stage);
			if (node.op == Op::literal && node.bit.wire)
				result.literals.push_back(node.bit);
			if (node.a >= 0)
				pending.push_back(node.a);
			if (node.b >= 0)
				pending.push_back(node.b);
			if (node.select >= 0)
				pending.push_back(node.select);
		}
		return result;
	}

	pool<Cell *> producers;

	PmuxSelectTree(const PmuxCoarseIndex &index, const PmuxEncoding &encoding) : index(index), encoding(encoding) {}

	int literal(SigBit bit)
	{
		auto found = literals.find(bit);
		if (found != literals.end())
			return found->second;
		int id = GetSize(nodes);
		nodes.push_back({Op::literal, -1, -1, -1, 0, bit});
		literals[bit] = id;
		return id;
	}

	bool constant(int id, State value) const { return nodes[id].op == Op::literal && nodes[id].bit == value; }
	int fold(SigBit bit, int code) { return specialize(bit, code, 12); }

	int select(int control, int level, int a, int b)
	{
		return mux(a, b, literal(encoding.controls[control]), -1 - level);
	}

	int column(std::vector<int> values, const std::vector<int> &controls)
	{
		log_assert(GetSize(values) == 1 << GetSize(controls));
		for (int level = 0, size = GetSize(values) / 2; size != 0; ++level, size /= 2)
			for (int row = 0; row < size; ++row)
				values[row] = select(controls[level], level, values[2 * row], values[2 * row + 1]);
		return values.front();
	}

	pool<SigBit> inputs(const Analysis &analysis) const
	{
		// 保持旧的可达节点集合遍历顺序。
		return pool<SigBit>(analysis.literals.rbegin(), analysis.literals.rend());
	}

	SigSpec emit(Module *module, const std::vector<int> &roots, const std::string &src, const Analysis &analysis) const
	{
		std::vector<SigBit> signals(GetSize(nodes));
		std::map<std::tuple<int, Op, int>, std::vector<int>> groups;
		for (int id = 0; id < GetSize(analysis.live); ++id) {
			if (!analysis.live[id])
				continue;
			const auto &node = nodes[id];
			if (node.op == Op::literal)
				signals[id] = node.bit;
			else
				groups[{node.stage < 0 ? analysis.data_end - node.stage : node.stage, node.op, node.select}].push_back(id);
		}
		for (const auto &[key, ids] : groups) {
			const auto &[stage, op, select] = key;
			SigSpec a, b;
			// 同一组的输出位按节点编号排列。
			Wire *out = module->addWire(NEW_ID, GetSize(ids));
			for (int i = 0; i < GetSize(ids); ++i) {
				const auto &node = nodes[ids[i]];
				a.append(signals[node.a]);
				if (node.b >= 0)
					b.append(signals[node.b]);
				signals[ids[i]] = SigBit(out, i);
			}
			switch (op) {
			case Op::invert: module->addNot(NEW_ID, a, out, false, src); break;
			case Op::bit_and: module->addAnd(NEW_ID, a, b, out, false, src); break;
			case Op::bit_or: module->addOr(NEW_ID, a, b, out, false, src); break;
			case Op::bit_xor: module->addXor(NEW_ID, a, b, out, false, src); break;
			case Op::bit_xnor: module->addXnor(NEW_ID, a, b, out, false, src); break;
			case Op::mux: module->addMux(NEW_ID, a, b, signals[select], out, src); break;
			case Op::literal: log_abort();
			}
		}
		SigSpec output;
		for (int id : roots)
			output.append(signals[id]);
		return output;
	}
};

YOSYS_NAMESPACE_END

#endif

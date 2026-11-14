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
		std::optional<int> a, b, select;
		int level;
		bool control;
		SigBit bit;
	};
	PmuxCoarseIndex &index;
	const PmuxEncoding &encoding;
	std::vector<Node> nodes;
	dict<SigBit, int> literals;
	dict<std::tuple<bool, int, Op, int, std::optional<int>, std::optional<int>>, int> operations;
	dict<std::pair<SigBit, int>, int> specialized;
	pool<SigBit> active;
	int visits_left = 65536;
	size_t truncated = 0;

	int operation(Op op, int a, std::optional<int> b, std::optional<int> select, int level, bool control)
	{
		if (op != Op::mux && b && *b < a)
			std::swap(a, *b);
		auto key = std::make_tuple(control, level, op, a, b, select);
		auto previous = operations.find(key);
		if (previous != operations.end())
			return previous->second;
		int id = GetSize(nodes);
		nodes.push_back({op, a, b, select, level, control, SigBit()});
		operations[key] = id;
		return id;
	}

	int invert(int a)
	{
		if (constant(a, State::S0) || constant(a, State::S1))
			return literal(constant(a, State::S0) ? State::S1 : State::S0);
		if (nodes[a].op == Op::invert)
			return *nodes[a].a;
		return operation(Op::invert, a, {}, {}, nodes[a].level + 1, false);
	}

	int gate(Op op, int a, int b)
	{
		if (constant(a, State::S0) || constant(a, State::S1))
			std::swap(a, b);
		if (constant(b, State::S0) || constant(b, State::S1)) {
			bool high = constant(b, State::S1);
			if (op == Op::bit_and || op == Op::bit_or)
				return high == (op == Op::bit_or) ? b : a;
			return high == (op == Op::bit_xor) ? invert(a) : a;
		}
		return operation(op, a, b, {}, std::max(nodes[a].level, nodes[b].level) + 1, false);
	}

	bool cannot_output_z(int id)
	{
		const auto &node = nodes[id];
		if (node.op == Op::mux)
			return cannot_output_z(*node.a) && cannot_output_z(*node.b);
		if (node.op != Op::literal)
			return true;
		if (!node.bit.wire)
			return node.bit != State::Sz;
		auto source = index.source(node.bit);
		return source && source->port == ID::Y &&
			source->cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($logic_not),
				ID($logic_and), ID($logic_or), ID($reduce_bool), ID($reduce_or), ID($reduce_and),
				ID($reduce_xor), ID($reduce_xnor), ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge));
	}

	std::optional<Cell *> complementary(int value, int inverse)
	{
		const auto &node = nodes[inverse];
		if (node.op == Op::invert && node.a == value && cannot_output_z(value))
			return nullptr;
		if (node.op != Op::literal || !node.bit.wire || nodes[value].op != Op::literal)
			return std::nullopt;
		auto source = index.source(node.bit);
		if (source && source->port == ID::Y && source->cell->type == ID($not) &&
				operand(source->cell, ID::A, source->offset, pmux_is_signed_port(source->cell, ID::A)) == nodes[value].bit &&
				cannot_output_z(value))
			return source->cell;
		return std::nullopt;
	}

	int mux(int a, int b, int select, int level, bool control)
	{
		if (a == b || constant(select, State::S0))
			return a;
		if (constant(select, State::S1))
			return b;
		if (constant(a, State::S0) && constant(b, State::S1))
			return select;
		// 高阻态可通过 mux 原样输出，按位异或会将其转成未知值。
		for (bool inverse : {false, true}) {
			if (auto producer = complementary(a, b)) {
				if (*producer)
					producers.insert(*producer);
				return operation(inverse ? Op::bit_xnor : Op::bit_xor, a, select, {}, level, control);
			}
			std::swap(a, b);
		}
		return operation(Op::mux, a, b, select, level, control);
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
		auto control = encoding.slots().find(bit);
		if (control != encoding.slots().end())
			return literal(code & (1 << control->second) ? State::S1 : State::S0);
		int original = literal(bit);
		if (!bit.wire)
			return original;
		auto key = std::make_pair(bit, code);
		auto cached = specialized.find(key);
		if (cached != specialized.end())
			return cached->second;
		if (depth == 0 || visits_left == 0) {
			++truncated;
			return original;
		}
		auto source = index.source(bit);
		if (!source || source->port != ID::Y)
			return original;
		if (!active.insert(bit).second) {
			++truncated;
			return original;
		}
		size_t cutoffs = truncated;
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
					result = mux(left, right, select, std::max({nodes[left].level, nodes[right].level, nodes[select].level}) + 1, false);
			}
		} else if (cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor))) {
			bool unary = cell->type == ID($not);
			bool sign = pmux_is_signed_port(cell, ID::A) && (unary || pmux_is_signed_port(cell, ID::B));
			SigBit a = operand(cell, ID::A, offset, sign);
			int left = specialize(a, code, depth - 1);
			if (unary) {
				if (left != literal(a))
					result = invert(left);
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
		if (cutoffs == truncated)
			specialized[key] = result;
		if (result != original)
			producers.insert(cell);
		return result;
	}

public:
	struct Analysis {
		std::vector<bool> live;
		int mux_bits = 0;
	};

	Analysis analyze(const std::vector<int> &roots) const
	{
		Analysis result;
		result.live.resize(nodes.size());
		std::vector<int> pending = roots;
		while (!pending.empty()) {
			int id = pending.back();
			pending.pop_back();
			log_assert(id >= 0 && id < GetSize(nodes));
			if (result.live[id])
				continue;
			result.live[id] = true;
			const auto &node = nodes[id];
			result.mux_bits += node.op == Op::mux;
			for (auto input : {node.a, node.b, node.select})
				if (input)
					pending.push_back(*input);
		}
		return result;
	}

	pool<Cell *> producers;

	PmuxSelectTree(PmuxCoarseIndex &index, const PmuxEncoding &encoding) : index(index), encoding(encoding) {}

	int literal(SigBit bit)
	{
		auto found = literals.find(bit);
		if (found != literals.end())
			return found->second;
		int id = GetSize(nodes);
		nodes.push_back({Op::literal, {}, {}, {}, 0, false, bit});
		literals[bit] = id;
		return id;
	}

	bool constant(int id, State value) const { return nodes[id].op == Op::literal && nodes[id].bit == value; }
	int fold(SigBit bit, int code) { return specialize(bit, code, 12); }

	int select(int control, int level, int a, int b)
	{
		log_assert(control >= 0 && control < GetSize(encoding.controls()) && level >= 0);
		return mux(a, b, literal(encoding.controls()[control]), level, true);
	}

	int column(std::vector<int> values, const std::vector<int> &controls)
	{
		log_assert(GetSize(values) == pmux_encoding_limit(GetSize(controls)));
		for (int level = 0, size = GetSize(values) / 2; size != 0; ++level, size /= 2)
			for (int row = 0; row < size; ++row)
				values[row] = select(controls[level], level, values[2 * row], values[2 * row + 1]);
		return values.front();
	}

	SigSpec emit(Module *module, const std::vector<int> &roots, const std::string &src, const Analysis &analysis) const
	{
		log_assert(analysis.live.size() == nodes.size());
		std::vector<std::optional<SigBit>> signals(nodes.size());
		std::map<std::tuple<bool, int, Op, std::optional<int>>, std::vector<int>> groups;
		for (int id = 0; id < GetSize(analysis.live); ++id) {
			if (!analysis.live[id])
				continue;
			const auto &node = nodes[id];
			if (node.op == Op::literal)
				signals[id] = node.bit;
			else
				groups[{node.control, node.level, node.op, node.select}].push_back(id);
		}
		auto signal = [&](std::optional<int> id) {
			log_assert(id && *id >= 0 && *id < GetSize(signals) && signals[*id]);
			return *signals[*id];
		};
		for (const auto &[key, ids] : groups) {
			Op op = std::get<2>(key);
			SigSpec a, b;
			// 同一组的输出位按节点编号排列。
			Wire *out = module->addWire(NEW_ID, GetSize(ids));
			for (int i = 0; i < GetSize(ids); ++i) {
				const auto &node = nodes[ids[i]];
				a.append(signal(node.a));
				if (node.b)
					b.append(signal(node.b));
				signals[ids[i]] = SigBit(out, i);
			}
			switch (op) {
			case Op::invert: module->addNot(NEW_ID, a, out, false, src); break;
			case Op::bit_and: case Op::bit_or: case Op::bit_xor: case Op::bit_xnor:
				pmux_emit_bitwise_choice(module, op == Op::bit_and ? ID($and) : op == Op::bit_or ? ID($or) :
						op == Op::bit_xor ? ID($xor) : ID($xnor), a, b, out, src);
				break;
			case Op::mux: module->addMux(NEW_ID, a, b, signal(std::get<3>(key)), out, src); break;
			case Op::literal: log_abort();
			}
		}
		SigSpec output;
		for (int id : roots)
			output.append(signal(id));
		return output;
	}
};

YOSYS_NAMESPACE_END

#endif

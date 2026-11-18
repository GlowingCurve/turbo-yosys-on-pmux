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

// 基础设施层的选择树构造工具。按控制编码折叠数据并共享子树，将相同层级的运算合并为多比特单元。

#ifndef YOSYS_PMUX_SELECT_TREE_H
#define YOSYS_PMUX_SELECT_TREE_H

#include "passes/opt/pmux_encoding.h"

#include <map>
#include <tuple>
#include <vector>

YOSYS_NAMESPACE_BEGIN

// 在统一的节点表中共享控制条件和数据表达式。
class PmuxSelectTree
{
      public:
	// 记录最终输出可到达的节点及其中的选择位数量。
	struct Analysis {
		std::vector<bool> live;
		int mux_bits = 0;
	};

	// 从各输出反向标记实际使用的运算。
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

	// 绑定模块索引和当前分组的控制编码。
	PmuxSelectTree(PmuxCoarseIndex &index, const PmuxEncoding &encoding)
	    : index(index), control_bits(encoding.controls()), control_slots(encoding.slots())
	{
	}

	// 为信号或常量取得可共享的叶子节点。
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

	// 检查指定节点是否表示给定的四态常量。
	bool constant(int id, State value) const { return nodes[id].op == Op::literal && nodes[id].bit == value; }
	// 按给定编码折叠一位数据。
	int fold(SigBit bit, int code) { return specialize(bit, code, 12); }

	// 用指定控制位连接同一层的两个子树。
	int select(int control, int level, int a, int b)
	{
		log_assert(control >= 0 && control < GetSize(control_bits) && level >= 0);
		return mux(a, b, literal(control_bits[control]), level, true);
	}

	// 按给定控制顺序逐层合并一列数据。
	int column(std::vector<int> values, const std::vector<int> &controls)
	{
		log_assert(GetSize(values) == pmux_encoding_limit(GetSize(controls)));
		for (int level = 0, size = GetSize(values) / 2; size != 0; ++level, size /= 2)
			for (int row = 0; row < size; ++row)
				values[row] = select(controls[level], level, values[2 * row], values[2 * row + 1]);
		return values.front();
	}

	// 将仍然使用的选择树节点转换为网表单元。
	SigSpec emit(Module *module, const std::vector<int> &roots, const std::string &src, const Analysis &analysis) const
	{
		log_assert(analysis.live.size() == nodes.size());
		std::vector<std::optional<SigBit>> signals(nodes.size());
		auto groups = group_live_nodes(analysis, signals);
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
			case Op::invert:
				module->addNot(NEW_ID, a, out, false, src);
				break;
			case Op::bit_and:
			case Op::bit_or:
			case Op::bit_xor:
			case Op::bit_xnor:
				pmux_emit_bitwise_choice(module, gate_type(op), a, b, out, src);
				break;
			case Op::mux:
				module->addMux(NEW_ID, a, b, signal(std::get<3>(key)), out, src);
				break;
			case Op::literal:
				log_abort();
			}
		}
		SigSpec output;
		for (int id : roots)
			output.append(signal(id));
		return output;
	}

      private:
	enum class Op { literal, invert, bit_and, bit_or, bit_xor, bit_xnor, mux };
	// 按运算、层级与选择信号分组，相同组可写入同一个多比特单元。
	using NodeGroups = std::map<std::tuple<bool, int, Op, std::optional<int>>, std::vector<int>>;

	// 将控制条件和运算类型相同的同层节点归入一组。
	NodeGroups group_live_nodes(const Analysis &analysis, std::vector<std::optional<SigBit>> &signals) const
	{
		NodeGroups groups;
		for (int id = 0; id < GetSize(analysis.live); ++id) {
			if (!analysis.live[id])
				continue;
			const auto &node = nodes[id];
			if (node.op == Op::literal)
				signals[id] = node.bit;
			else
				groups[{node.control, node.level, node.op, node.select}].push_back(id);
		}
		return groups;
	}

	// 记录节点的操作数、逻辑层级和选择信号。
	struct Node {
		Op op;
		std::optional<int> a, b, select;
		int level;
		bool control;
		SigBit bit;
	};
	PmuxCoarseIndex index;
	std::vector<SigBit> control_bits;
	dict<SigBit, int> control_slots;
	std::vector<Node> nodes;
	dict<SigBit, int> literals;
	dict<std::tuple<bool, int, Op, int, std::optional<int>, std::optional<int>>, int> operations;
	dict<std::pair<SigBit, int>, int> specialized;
	pool<SigBit> active;
	int visits_left = 65536;
	size_t truncated = 0;

	// 复用相同运算，交换律运算使用固定的输入顺序。
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

	// 化简常量反相和连续两次反相。
	int invert(int a)
	{
		if (constant(a, State::S0) || constant(a, State::S1))
			return literal(constant(a, State::S0) ? State::S1 : State::S0);
		if (nodes[a].op == Op::invert)
			return *nodes[a].a;
		return operation(Op::invert, a, {}, {}, nodes[a].level + 1, false);
	}

	// 利用单比特常量化简按位运算。
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

	// 检查数据路径是否可能传递高阻态。
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
		       source->cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($logic_not), ID($logic_and), ID($logic_or),
					     ID($reduce_bool), ID($reduce_or), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor), ID($eq), ID($ne),
					     ID($lt), ID($le), ID($gt), ID($ge));
	}

	// 识别互补信号，要求异或改写能保留高阻态语义。
	std::optional<Cell *> complementary(int value, int inverse)
	{
		const auto &node = nodes[inverse];
		if (node.op == Op::invert && node.a == value && cannot_output_z(value))
			return nullptr;
		if (node.op != Op::literal || !node.bit.wire || nodes[value].op != Op::literal)
			return std::nullopt;
		auto source = index.source(node.bit);
		if (source && source->port == ID::Y && source->cell->type == ID($not) &&
		    index.port_bit(source->cell, ID::A, source->offset, pmux_cell_signed(source->cell)) == nodes[value].bit && cannot_output_z(value))
			return source->cell;
		return std::nullopt;
	}

	// 化简相同分支、常量控制和互补分支。
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
			auto producer = complementary(a, b);
			if (producer) {
				if (*producer)
					producers.insert(*producer);
				return operation(inverse ? Op::bit_xnor : Op::bit_xor, a, select, {}, level, control);
			}
			std::swap(a, b);
		}
		return operation(Op::mux, a, b, select, level, control);
	}

	// 将按位运算单元转换为选择树中的对应节点。
	static Op gate_op(IdString type)
	{
		if (type == ID($and))
			return Op::bit_and;
		if (type == ID($or))
			return Op::bit_or;
		if (type == ID($xor))
			return Op::bit_xor;
		log_assert(type == ID($xnor));
		return Op::bit_xnor;
	}

	// 取得生成逻辑单元所需的 RTLIL 类型。
	static IdString gate_type(Op op)
	{
		switch (op) {
		case Op::bit_and:
			return ID($and);
		case Op::bit_or:
			return ID($or);
		case Op::bit_xor:
			return ID($xor);
		case Op::bit_xnor:
			return ID($xnor);
		default:
			log_abort();
		}
	}

	// 在给定控制编码下递归折叠单元输入，保留尚未确定的数据位。
	int specialize_cell(Cell *cell, int offset, int original, int code, int depth)
	{
		int result = original;
		if (cell->type == ID($mux) && pmux_select_shape(cell)) {
			SigBit sel = index.port(cell, ID::S)[0];
			int select = specialize(sel, code, depth - 1);
			SigBit a = index.port_bit(cell, ID::A, offset, false);
			SigBit b = index.port_bit(cell, ID::B, offset, false);
			if (constant(select, State::S0) || constant(select, State::S1))
				result = specialize(constant(select, State::S0) ? a : b, code, depth - 1);
			else {
				int left = specialize(a, code, depth - 1);
				int right = specialize(b, code, depth - 1);
				if (left != literal(a) || right != literal(b) || select != literal(sel))
					result =
					  mux(left, right, select, std::max({nodes[left].level, nodes[right].level, nodes[select].level}) + 1, false);
			}
		} else if (cell->type.in(ID($not), ID($and), ID($or), ID($xor), ID($xnor))) {
			bool unary = cell->type == ID($not);
			bool sign = pmux_cell_signed(cell);
			SigBit a = index.port_bit(cell, ID::A, offset, sign);
			int left = specialize(a, code, depth - 1);
			if (unary) {
				if (left != literal(a))
					result = invert(left);
			} else {
				SigBit b = index.port_bit(cell, ID::B, offset, sign);
				int right = specialize(b, code, depth - 1);
				if (left != literal(a) || right != literal(b)) {
					Op op = gate_op(cell->type);
					result = gate(op, left, right);
				}
			}
		}
		return result;
	}

	// 在访问预算内传播控制常量，并缓存完整的折叠结果。
	int specialize(SigBit bit, int code, int depth)
	{
		auto control = control_slots.find(bit);
		if (control != control_slots.end())
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
		int result = specialize_cell(cell, source->offset, original, code, depth);
		active.erase(bit);
		if (cutoffs == truncated)
			specialized[key] = result;
		if (result != original)
			producers.insert(cell);
		return result;
	}
};

YOSYS_NAMESPACE_END

#endif

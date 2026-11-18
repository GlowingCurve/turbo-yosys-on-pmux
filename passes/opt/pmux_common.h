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

// 基础设施层的公共工具。各项优化在这里统一读取符号属性、处理四态逻辑和生成基本单元。

#ifndef YOSYS_PMUX_COMMON_H
#define YOSYS_PMUX_COMMON_H

#include "kernel/modtools.h"

#include <algorithm>
#include <optional>
#include <string>
#include <utility>
#include <vector>

YOSYS_NAMESPACE_BEGIN

// 六个控制位的全部二值组合可放入一个 64 位真值表。
inline constexpr int pmux_max_controls = 6;
inline constexpr int pmux_max_rows = 1 << pmux_max_controls;
// 限制一次选择树重建处理的数据位数和比较输出列的次数。
inline constexpr int pmux_max_table_bits = 32768;
inline constexpr int pmux_max_pair_checks = 32768;

// 返回给定控制位数对应的完整编码数。
inline int pmux_encoding_limit(int controls)
{
	log_assert(controls >= 0 && controls <= pmux_max_controls);
	return 1 << controls;
}

// 跳过会观察未知值的电路，依次处理选中的模块并记录改写次数。
template <typename Fn> void pmux_run_pass(Design *design, const char *pass_name, const char *header, Fn &&run_module)
{
	design->scratchpad_unset("opt.did_something");
	log_header(design, "%s", header);
	// 管理本次 Pass 日志的缩进层级。
	struct LogScope {
		// 进入当前 Pass 的日志层级。
		LogScope() { log_push(); }
		// 退出当前 Pass 的日志层级。
		~LogScope() { log_pop(); }
	} scope;
	// 上层模块可能观察到未知值或高阻态，此时保留原电路。
	for (auto module : design->modules())
		for (auto cell : module->cells())
			if (cell->type.in(ID($eqx), ID($nex), ID($bweqx)) || StaticCellTypes::categories.is_tristate(cell->type))
				return;

	int rewrites = 0;
	for (auto module : design->selected_modules()) {
		if (module->get_blackbox_attribute() || !module->processes.empty() ||
		    (!design->selected_whole_module(module) && module->selected_cells().empty()))
			continue;
		int module_rewrites = run_module(module);
		if (module_rewrites)
			log("  %s in %s: %d rewrites.\n", pass_name, log_id(module), module_rewrites);
		rewrites += module_rewrites;
	}
	if (rewrites)
		design->scratchpad_set_bool("opt.did_something", true);
}

// 识别有时钟输入的内建触发器。
inline bool pmux_is_clocked_ff(const Cell *cell)
{
	if (!yosys_celltypes.cell_known(cell->type) || !StaticCellTypes::categories.is_ff(cell->type) || cell->type.in(ID($ff), ID($_FF_)))
		return false;
	const auto &inputs = StaticCellTypes::port_info.inputs(cell->type);
	return inputs.contains(ID::CLK) || inputs.contains(ID::C);
}

// 读取操作数端口的符号属性。
inline bool pmux_is_signed_port(const Cell *cell, IdString port)
{
	if (!port.in(ID::A, ID::B))
		return false;
	auto sign = port == ID::A ? ID::A_SIGNED : ID::B_SIGNED;
	return cell->hasParam(sign) && cell->getParam(sign).as_bool();
}

// 双输入运算仅在两个操作数都有符号时进行符号扩展。
inline bool pmux_cell_signed(const Cell *cell)
{
	return pmux_is_signed_port(cell, ID::A) && (!cell->hasPort(ID::B) || pmux_is_signed_port(cell, ID::B));
}

// 检查端口是否为选择器的控制输入。
inline bool pmux_has_selection_port(const Cell *cell, IdString port)
{
	return port == ID::S && cell->type.in(ID($mux), ID($pmux)) && cell->hasPort(port);
}

// 按比较器的符号规则准备等宽的两个操作数。
inline std::optional<std::pair<SigSpec, SigSpec>> pmux_comparison_operands(const Cell *cell, int max_width, const SigMap &sigmap)
{
	log_assert(cell->type.in(ID($eq), ID($ne), ID($logic_not)));
	bool unary = cell->type == ID($logic_not);
	auto a = sigmap(cell->getPort(ID::A));
	auto b = unary ? SigSpec(State::S0, GetSize(a)) : sigmap(cell->getPort(ID::B));
	int width = std::max(GetSize(a), GetSize(b));
	if (width > max_width)
		return std::nullopt;
	bool sign = !unary && pmux_cell_signed(cell);
	a.extend_u0(width, sign);
	b.extend_u0(width, sign);
	return std::make_pair(std::move(a), std::move(b));
}

// 判断输入能否通过组合路径影响当前输出。
inline bool pmux_combinational_input(IdString type, IdString port)
{
	if (type.in(ID($ff), ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce)))
		return false;
	if (type.in(ID($adff), ID($adffe)))
		return port == ID::ARST;
	if (type.in(ID($aldff), ID($aldffe)))
		return port.in(ID::ALOAD, ID::AD);
	if (type.in(ID($dffsr), ID($dffsre)))
		return port.in(ID::SET, ID::CLR);
	return true;
}

// 按四态逻辑计算单比特运算结果。
inline State pmux_eval_bitwise(IdString type, State a, State b)
{
	if (type == ID($and)) {
		if (a == State::S0 || b == State::S0)
			return State::S0;
		return a == State::S1 && b == State::S1 ? State::S1 : State::Sx;
	}
	if (type == ID($or)) {
		if (a == State::S1 || b == State::S1)
			return State::S1;
		return a == State::S0 && b == State::S0 ? State::S0 : State::Sx;
	}
	log_assert(type.in(ID($xor), ID($xnor)));
	if ((a != State::S0 && a != State::S1) || (b != State::S0 && b != State::S1))
		return State::Sx;
	return ((a != b) == (type == ID($xor))) ? State::S1 : State::S0;
}

// 优先化简常量选择和相同输入，再生成二选一单元。
inline SigSpec pmux_emit_mux(Module *module, const SigSpec &sel, const SigSpec &d0, const SigSpec &d1, const std::string &src = {})
{
	log_assert(GetSize(sel) == 1 && GetSize(d0) == GetSize(d1));
	if (d0 == d1 || sel[0] == State::S0)
		return d0;
	if (sel[0] == State::S1)
		return d1;
	return module->Mux(NEW_ID, d0, d1, sel, src);
}

// 为一组输出位生成同类按位运算。
inline SigSpec pmux_emit_bitwise_choice(Module *module, IdString gate, const SigSpec &a, const SigSpec &b, SigSpec output = {},
					const std::string &src = {})
{
	auto name = NEW_ID;
	if (output.empty())
		output = module->addWire(NEW_ID, std::max(GetSize(a), GetSize(b)));
	if (gate == ID($and))
		module->addAnd(name, a, b, output, false, src);
	else if (gate == ID($or))
		module->addOr(name, a, b, output, false, src);
	else if (gate == ID($xor))
		module->addXor(name, a, b, output, false, src);
	else {
		log_assert(gate == ID($xnor));
		module->addXnor(name, a, b, output, false, src);
	}
	return output;
}

// 按指定类型构造归约或反相单元，返回单元以便后续记录其名称。
inline Cell *pmux_emit_reduce(Module *module, IdString type, const SigSpec &input, SigSpec output = {}, const std::string &src = {})
{
	if (output.empty())
		output = module->addWire(NEW_ID, type == ID($not) ? GetSize(input) : 1);
	auto name = NEW_ID;
	if (type == ID($not))
		return module->addNot(name, input, output, false, src);
	if (type == ID($reduce_and))
		return module->addReduceAnd(name, input, output, false, src);
	if (type == ID($reduce_or))
		return module->addReduceOr(name, input, output, false, src);
	if (type == ID($reduce_xor))
		return module->addReduceXor(name, input, output, false, src);
	log_assert(type == ID($reduce_xnor));
	return module->addReduceXnor(name, input, output, false, src);
}

YOSYS_NAMESPACE_END

#endif

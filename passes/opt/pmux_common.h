#ifndef YOSYS_PMUX_COMMON_H
#define YOSYS_PMUX_COMMON_H

#include "kernel/modtools.h"

#include <algorithm>
#include <optional>

YOSYS_NAMESPACE_BEGIN

inline constexpr int pmux_max_controls = 6;
inline constexpr int pmux_max_rows = 1 << pmux_max_controls;
inline constexpr int pmux_max_table_bits = 32768;
inline constexpr int pmux_max_pair_checks = 32768;

inline int pmux_encoding_limit(int controls)
{
	log_assert(controls >= 0 && controls <= pmux_max_controls);
	return 1 << controls;
}

template<typename Fn>
void pmux_run_pass(Design *design, const char *pass_name, const char *header, Fn &&run_module)
{
	design->scratchpad_unset("opt.did_something");
	log_header(design, "%s", header);
	// Undefined values may be observed through a hierarchy boundary.
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

inline bool pmux_is_clocked_ff(const Cell *cell)
{
	if (!yosys_celltypes.cell_known(cell->type) || !StaticCellTypes::categories.is_ff(cell->type) ||
			cell->type.in(ID($ff), ID($_FF_)))
		return false;
	const auto &inputs = StaticCellTypes::port_info.inputs(cell->type);
	return inputs.contains(ID::CLK) || inputs.contains(ID::C);
}

inline bool pmux_is_signed_port(const Cell *cell, IdString port)
{
	if (!port.in(ID::A, ID::B))
		return false;
	auto sign = port == ID::A ? ID::A_SIGNED : ID::B_SIGNED;
	return cell->hasParam(sign) && cell->getParam(sign).as_bool();
}

inline bool pmux_has_selection_port(const Cell *cell, IdString port)
{
	return port == ID::S && cell->type.in(ID($mux), ID($pmux)) && cell->hasPort(port);
}

inline std::optional<std::pair<SigSpec, SigSpec>> pmux_comparison_operands(const Cell *cell, int max_width, const SigMap &sigmap)
{
	log_assert(cell->type.in(ID($eq), ID($ne), ID($logic_not)));
	bool unary = cell->type == ID($logic_not);
	auto a = sigmap(cell->getPort(ID::A));
	auto b = unary ? SigSpec(State::S0, GetSize(a)) : sigmap(cell->getPort(ID::B));
	int width = std::max(GetSize(a), GetSize(b));
	if (width > max_width)
		return std::nullopt;
	bool sign = !unary && pmux_is_signed_port(cell, ID::A) && pmux_is_signed_port(cell, ID::B);
	a.extend_u0(width, sign);
	b.extend_u0(width, sign);
	return std::make_pair(std::move(a), std::move(b));
}

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

inline SigSpec pmux_emit_mux(Module *module, const SigSpec &sel, const SigSpec &d0, const SigSpec &d1, const std::string &src = {})
{
	log_assert(GetSize(sel) == 1 && GetSize(d0) == GetSize(d1));
	if (d0 == d1 || sel[0] == State::S0)
		return d0;
	if (sel[0] == State::S1)
		return d1;
	return module->Mux(NEW_ID, d0, d1, sel, src);
}

inline SigSpec pmux_emit_bitwise_choice(Module *module, IdString gate, const SigSpec &a, const SigSpec &b,
		SigSpec output = {}, const std::string &src = {})
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

YOSYS_NAMESPACE_END

#endif

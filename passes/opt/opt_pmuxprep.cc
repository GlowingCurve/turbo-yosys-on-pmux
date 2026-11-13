/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/register.h"
#include "kernel/log.h"
#include "kernel/rtlil.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool reduce_candidate(IdString type)
{
	return type.in(ID($reduce_and), ID($reduce_or), ID($mux), ID($pmux), ID($bmux), ID($demux));
}

struct MuxCandidates {
	bool muxtree = false;
	bool reduce = false;
};

MuxCandidates find_mux_candidates(Design *design)
{
	MuxCandidates candidates;
	for (auto module : design->selected_unboxed_modules()) {
		if (!design->selected_whole_module(module) || !module->processes.empty())
			return {true, false};
		for (auto cell : module->cells()) {
			if (cell->type.in(ID($mux), ID($pmux)))
				return {true, false};
			if (!candidates.reduce)
				candidates.reduce = reduce_candidate(cell->type);
		}
	}
	return candidates;
}

bool needs_reduce(Design *design)
{
	for (auto module : design->selected_unboxed_modules()) {
		for (auto cell : module->cells())
			if (reduce_candidate(cell->type) && design->selected(module, cell))
				return true;
	}
	return false;
}

bool has_init_wire(Module *module)
{
	// opt_dff 检查所选模块内全部线网的初始值。
	for (auto wire : module->wires())
		if (wire->attributes.count(ID::init))
			return true;
	return false;
}

struct ShareCandidates {
	bool share = false;
	bool dff = false;
};

ShareCandidates find_share_candidates(Design *design, bool check_dff)
{
	ShareCandidates candidates;
	auto modules = design->selected_unboxed_modules();
	for (auto module : modules) {
		bool has_mux = false;
		int operators = 0;
		for (auto cell : module->cells()) {
			if (!design->selected(module, cell))
				continue;
			has_mux |= cell->type.in(ID($mux), ID($pmux), ID($_MUX_));
			// The ALU's port requirements are checked by opt_share itself.
			if (operators < 2 && cell->type.in(
					ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_),
					ID($and), ID($or), ID($xor), ID($xnor), ID($logic_and), ID($logic_or),
					ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
					ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt),
					ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($concat), ID($alu)))
				++operators;
			if (has_mux && operators == 2)
				return {true, false};
			if (check_dff && !candidates.dff && cell->is_builtin_ff())
				candidates.dff = true;
		}
	}
	if (check_dff && !candidates.dff)
		for (auto module : modules)
			if (has_init_wire(module))
				return {false, true};
	return candidates;
}

bool needs_dff(Design *design)
{
	for (auto module : design->selected_unboxed_modules()) {
		for (auto cell : module->cells())
			if (cell->is_builtin_ff() && design->selected(module, cell))
				return true;
		if (has_init_wire(module))
			return true;
	}
	return false;
}

struct OptPmuxPrepPass : public Pass {
	OptPmuxPrepPass() : Pass("opt_pmuxprep", "perform simple optimizations with candidate checks") { }

	void help() override
	{
		log("\n");
		log("    opt_pmuxprep [options] [selection]\n");
		log("\n");
		log("Run the opt pipeline with checks for candidates before opt_muxtree,\n");
		log("opt_reduce, opt_share and opt_dff. The options are the same as for opt.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		std::string opt_clean_args;
		std::string opt_expr_args;
		std::string opt_reduce_args;
		std::string opt_merge_args;
		std::string opt_dff_args;
		bool full_mode = false;
		bool fast_mode = false;
		bool noff_mode = false;
		bool hier_mode = false;
		bool keepdc_mode = false;
		bool sat_mode = false;

		log_header(design, "Executing OPT_PMUXPREP pass (performing simple optimizations).\n");
		log_push();

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-purge") {
				opt_clean_args += " -purge";
				continue;
			}
			if (args[argidx] == "-mux_undef") {
				opt_expr_args += " -mux_undef";
				continue;
			}
			if (args[argidx] == "-mux_bool") {
				opt_expr_args += " -mux_bool";
				continue;
			}
			if (args[argidx] == "-undriven") {
				opt_expr_args += " -undriven";
				continue;
			}
			if (args[argidx] == "-noclkinv") {
				opt_expr_args += " -noclkinv";
				continue;
			}
			if (args[argidx] == "-fine") {
				opt_expr_args += " -fine";
				opt_reduce_args += " -fine";
				continue;
			}
			if (args[argidx] == "-full") {
				opt_expr_args += " -full";
				opt_reduce_args += " -full";
				full_mode = true;
				continue;
			}
			if (args[argidx] == "-keepdc") {
				opt_expr_args += " -keepdc";
				opt_dff_args += " -keepdc";
				opt_merge_args += " -keepdc";
				keepdc_mode = true;
				continue;
			}
			if (args[argidx] == "-nodffe") {
				opt_dff_args += " -nodffe";
				continue;
			}
			if (args[argidx] == "-nosdff") {
				opt_dff_args += " -nosdff";
				continue;
			}
			if (args[argidx] == "-sat") {
				opt_dff_args += " -sat";
				sat_mode = true;
				continue;
			}
			if (args[argidx] == "-share_all") {
				opt_merge_args += " -share_all";
				continue;
			}
			if (args[argidx] == "-fast") {
				fast_mode = true;
				continue;
			}
			if (args[argidx] == "-noff") {
				noff_mode = true;
				continue;
			}
			if (args[argidx] == "-hier") {
				hier_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		// 无寄存器时也需要报告选项冲突。
		bool dff_option_conflict = sat_mode && keepdc_mode;
		auto run_dff = [&]() { Pass::call(design, "opt_dff" + opt_dff_args); };
		auto check_and_run_dff = [&]() {
			if (!noff_mode && (dff_option_conflict || needs_dff(design)))
				run_dff();
		};

		if (fast_mode) {
			while (1) {
				Pass::call(design, "opt_expr" + opt_expr_args);
				Pass::call(design, "opt_merge" + opt_merge_args);
				design->scratchpad_unset("opt.did_something");
				check_and_run_dff();
				if (!design->scratchpad_get_bool("opt.did_something"))
					break;
				if (hier_mode)
					Pass::call(design, "opt_hier");
				Pass::call(design, "opt_clean" + opt_clean_args);
				log_header(design, "Rerunning OPT_PMUXPREP passes. (Removed registers in this run.)\n");
			}
			Pass::call(design, "opt_clean" + opt_clean_args);
		} else {
			design->scratchpad_unset("opt.did_something");
			Pass::call(design, "opt_expr" + opt_expr_args);
			auto mux = find_mux_candidates(design);
			if (mux.muxtree || mux.reduce) {
				Pass::call(design, "opt_merge -nomux" + opt_merge_args);
				mux = find_mux_candidates(design);
			}
			bool needs_expr = design->scratchpad_get_bool("opt.did_something");
			while (1) {
				design->scratchpad_unset("opt.did_something");
				if (mux.muxtree) {
					Pass::call(design, "opt_muxtree");
					mux.reduce = needs_reduce(design);
				}
				if (mux.reduce)
					Pass::call(design, "opt_reduce" + opt_reduce_args);
				Pass::call(design, "opt_merge" + opt_merge_args);
				needs_expr |= design->scratchpad_get_bool("opt.did_something");
				// Without a mux-tree or reduction pass, opt_merge has already reached its fixed point.
				if (!mux.muxtree && !mux.reduce)
					design->scratchpad_unset("opt.did_something");
				if (full_mode) {
					auto candidates = find_share_candidates(design, !noff_mode && !dff_option_conflict);
					if (candidates.share)
						Pass::call(design, "opt_share");
					if (!noff_mode && (dff_option_conflict || (candidates.share ? needs_dff(design) : candidates.dff)))
						run_dff();
				} else {
					check_and_run_dff();
				}
				if (hier_mode)
					Pass::call(design, "opt_hier");
				Pass::call(design, "opt_clean" + opt_clean_args);
				if (!needs_expr && !design->scratchpad_get_bool("opt.did_something"))
					break;
				Pass::call(design, "opt_expr" + opt_expr_args);
				if (!design->scratchpad_get_bool("opt.did_something"))
					break;
				needs_expr = false;
				mux = find_mux_candidates(design);
				log_header(design, "Rerunning OPT_PMUXPREP passes. (Maybe there is more to do..)\n");
			}
		}

		design->optimize();
		design->check();

		log_header(design, "Finished OPT_PMUXPREP passes.%s\n", fast_mode ? "" : " (There is nothing left to do.)");
		log_pop();
	}
} OptPmuxPrepPass;

PRIVATE_NAMESPACE_END

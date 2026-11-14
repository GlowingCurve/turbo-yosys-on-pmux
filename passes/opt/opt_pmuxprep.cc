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

enum class Scan { Mux, Reduce, Share, Dff, ShareAndDff };

struct Candidates {
	bool muxtree = false;
	bool reduce = false;
	bool share = false;
	bool dff = false;
};

Candidates scan_candidates(Design *design, Scan scan)
{
	Candidates candidates;
	const bool check_share = scan == Scan::Share || scan == Scan::ShareAndDff;
	const bool check_dff = scan == Scan::Dff || scan == Scan::ShareAndDff;
	auto modules = design->selected_unboxed_modules();
	for (auto module : modules) {
		if (scan == Scan::Mux && (!design->selected_whole_module(module) || !module->processes.empty()))
			return {.muxtree = true};
		bool has_mux = false;
		int operators = 0;
		for (auto cell : module->cells()) {
			IdString type = cell->type;
			if (scan == Scan::Mux) {
				if (type.in(ID($mux), ID($pmux)))
					return {.muxtree = true};
				if (!candidates.reduce)
					candidates.reduce = reduce_candidate(type);
				continue;
			}
			if (!design->selected(module, cell))
				continue;
			if (scan == Scan::Reduce && reduce_candidate(type))
				return {.reduce = true};
			if (check_dff && !candidates.dff && cell->is_builtin_ff()) {
				candidates.dff = true;
				if (!check_share)
					return candidates;
			}
			if (!check_share)
				continue;
			has_mux |= type.in(ID($mux), ID($pmux), ID($_MUX_));
			// The ALU's port requirements are checked by opt_share itself.
			if (operators < 2 && type.in(
					ID($_AND_), ID($_NAND_), ID($_OR_), ID($_NOR_), ID($_XOR_), ID($_XNOR_), ID($_ANDNOT_), ID($_ORNOT_),
					ID($and), ID($or), ID($xor), ID($xnor), ID($logic_and), ID($logic_or),
					ID($shl), ID($shr), ID($sshl), ID($sshr), ID($shift), ID($shiftx),
					ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt),
					ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($concat), ID($alu)))
				++operators;
			if (has_mux && operators == 2)
				return {.share = true};
		}
	}
	if (check_dff && !candidates.dff) {
		// opt_dff reads init attributes from all wires in selected modules.
		for (auto module : modules)
			for (auto wire : module->wires())
				if (wire->attributes.count(ID::init))
					return {.dff = true};
	}
	return candidates;
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

		size_t argidx;
		for (argidx = 1; argidx < args.size(); ++argidx) {
			const auto &arg = args[argidx];
			if (arg == "-purge") {
				opt_clean_args += " -purge";
			} else if (arg == "-mux_undef" || arg == "-mux_bool" || arg == "-undriven" || arg == "-noclkinv") {
				opt_expr_args += " " + arg;
			} else if (arg == "-fine" || arg == "-full") {
				opt_expr_args += " " + arg;
				opt_reduce_args += " " + arg;
				full_mode |= arg == "-full";
			} else if (arg == "-keepdc") {
				opt_expr_args += " -keepdc";
				opt_dff_args += " -keepdc";
				opt_merge_args += " -keepdc";
				keepdc_mode = true;
			} else if (arg == "-nodffe" || arg == "-nosdff") {
				opt_dff_args += " " + arg;
			} else if (arg == "-sat") {
				opt_dff_args += " -sat";
				sat_mode = true;
			} else if (arg == "-share_all") {
				opt_merge_args += " -share_all";
			} else if (arg == "-fast") {
				fast_mode = true;
			} else if (arg == "-noff") {
				noff_mode = true;
			} else if (arg == "-hier") {
				hier_mode = true;
			} else {
				break;
			}
		}
		if (sat_mode && keepdc_mode)
			log_cmd_error("Options -sat and -keepdc are mutually exclusive.\n");
		extra_args(args, argidx, design);
		log_header(design, "Executing OPT_PMUXPREP pass (performing simple optimizations).\n");
		log_push();

		auto run_dff = [&]() { Pass::call(design, "opt_dff" + opt_dff_args); };
		auto check_and_run_dff = [&]() {
			if (!noff_mode && scan_candidates(design, Scan::Dff).dff)
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
			auto mux = scan_candidates(design, Scan::Mux);
			if (mux.muxtree || mux.reduce)
				Pass::call(design, "opt_merge -nomux" + opt_merge_args);
			bool needs_expr = design->scratchpad_get_bool("opt.did_something");
			while (1) {
				design->scratchpad_unset("opt.did_something");
				if (mux.muxtree) {
					Pass::call(design, "opt_muxtree");
					mux.reduce = scan_candidates(design, Scan::Reduce).reduce;
				}
				if (mux.reduce)
					Pass::call(design, "opt_reduce" + opt_reduce_args);
				Pass::call(design, "opt_merge" + opt_merge_args);
				needs_expr |= design->scratchpad_get_bool("opt.did_something");
				// Without a mux-tree or reduction pass, opt_merge has already reached its fixed point.
				if (!mux.muxtree && !mux.reduce)
					design->scratchpad_unset("opt.did_something");
				if (full_mode) {
					auto candidates = scan_candidates(design, noff_mode ? Scan::Share : Scan::ShareAndDff);
					if (candidates.share) {
						Pass::call(design, "opt_share");
						check_and_run_dff();
					} else if (candidates.dff) {
						run_dff();
					}
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
				mux = scan_candidates(design, Scan::Mux);
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

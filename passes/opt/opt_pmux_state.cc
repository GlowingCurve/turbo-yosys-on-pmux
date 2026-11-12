#include "kernel/ff.h"
#include "kernel/yosys.h"
#include "passes/opt/pmux_coarse.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

using StateCode = dict<SigBit, bool>;

bool clocked_ff(Cell *cell)
{
	return cell && cell->type.in(ID($dff), ID($dffe), ID($adff), ID($adffe), ID($sdff), ID($sdffe), ID($sdffce));
}

bool onehot(const Const &value)
{
	return value.is_fully_def() && std::count(value.begin(), value.end(), State::S1) == 1;
}

std::optional<StateCode> comparison(PmuxCoarseIndex &index, Cell *cell)
{
	if (!cell || !cell->type.in(ID($eq), ID($ne), ID($logic_not)) || GetSize(cell->getPort(ID::Y)) != 1)
		return std::nullopt;
	auto operands = index.comparison_operands(cell, 128);
	if (!operands)
		return std::nullopt;
	const auto &[a, b] = *operands;
	StateCode result;
	for (int offset = 0; offset < GetSize(a); ++offset) {
		SigBit bit = a[offset], value = b[offset];
		if (!bit.wire)
			std::swap(bit, value);
		if (value.wire || (value != State::S0 && value != State::S1))
			return std::nullopt;
		if (!bit.wire) {
			if (bit != value)
				return std::nullopt;
			continue;
		}
		bool high = value == State::S1;
		auto inserted = result.emplace(bit, high);
		if (!inserted.second && inserted.first->second != high)
			return std::nullopt;
	}
	return result;
}

class StateWorker
{
	Module *module;
	PmuxCoarseIndex index;
	FfInitVals initvals;

	bool onehot_next(const SigSpec &value, const pool<SigBit> &bits, pool<Cell *> &active,
			pool<SigSpec> &proven, int &budget, int depth)
	{
		if (--budget < 0 || depth > 16 || GetSize(value) != GetSize(bits))
			return false;
		if (proven.count(value))
			return true;
		if (value.is_fully_const())
			return onehot(value.as_const());
		if (pool<SigBit>(value.begin(), value.end()) == bits)
			return true;
		auto mux = index.driver(value[0]);
		if (!mux || mux->type != ID($mux) || index.port(mux, ID::Y) != value || !active.insert(mux).second)
			return false;
		for (auto bit : value)
			if (index.driver(bit) != mux)
				return false;
		if (!onehot_next(index.port(mux, ID::A), bits, active, proven, budget, depth + 1) ||
				!onehot_next(index.port(mux, ID::B), bits, active, proven, budget, depth + 1))
			return false;
		active.erase(mux);
		proven.insert(value);
		return true;
	}

	bool onehot_register(Cell *state)
	{
		FfData ff(&initvals, state);
		SigSpec q = index.sigmap(ff.sig_q);
		if (!ff.has_clk || ff.has_aload || ff.has_sr || GetSize(q) < 2 || GetSize(q) > 128 || !onehot(ff.val_init) ||
				(ff.has_arst && !onehot(ff.val_arst)) || (ff.has_srst && !onehot(ff.val_srst)))
			return false;
		pool<SigBit> bits(q.begin(), q.end());
		if (GetSize(bits) != GetSize(q))
			return false;
		for (auto bit : bits)
			if (index.driver(bit) != state)
				return false;
		pool<Cell *> active;
		pool<SigSpec> proven;
		int budget = 128;
		return onehot_next(index.sigmap(ff.sig_d), bits, active, proven, budget, 0);
	}

	void replace_decodes()
	{
		dict<Cell *, bool> onehot_states;
		std::vector<std::pair<Cell *, SigBit>> replacements;
		for (auto cell : module->selected_cells()) {
			if (!cell->type.in(ID($eq), ID($ne), ID($logic_not)) || !index.editable(cell) ||
					!initvals(cell->getPort(ID::Y)).is_fully_undef())
				continue;
			auto compare = comparison(index, cell);
			if (!compare || compare->empty())
				continue;
			auto state = index.driver(compare->begin()->first);
			if (!clocked_ff(state))
				continue;
			bool same_state = true;
			for (const auto &[bit, high] : *compare)
				same_state &= index.driver(bit) == state;
			if (!same_state)
				continue;
			auto status = onehot_states.emplace(state, false);
			if (status.second)
				status.first->second = onehot_register(state);
			if (!status.first->second)
				continue;
			SigSpec q = index.port(state, ID::Q);
			int required_ones = 0;
			for (const auto &literal : *compare)
				required_ones += literal.second;
			SigBit replacement(State::S0);
			int matches = 0;
			for (auto bit : q) {
				auto literal = compare->find(bit);
				bool mentioned = literal != compare->end();
				bool equal = mentioned ? literal->second && required_ones == 1 : required_ones == 0;
				if (equal != (cell->type == ID($ne))) {
					matches++;
					replacement = bit;
				}
			}
			if (matches == GetSize(q))
				replacement = State::S1;
			if (matches <= 1 || matches == GetSize(q))
				replacements.emplace_back(cell, replacement);
		}
		for (const auto &[cell, replacement] : replacements) {
			SigSpec y = cell->getPort(ID::Y);
			module->remove(cell);
			module->connect(y, replacement);
		}
		if (!replacements.empty())
			log("  %s: removed %d one-hot state decoders.\n", log_id(module), GetSize(replacements));
	}

	bool capture(Cell *bank, const SigSpec &clock, bool polarity, const SigSpec &q, SigSpec &data,
			SigBit &enable, pool<Cell *> &candidates)
	{
		if (!clocked_ff(bank) || index.port(bank, ID::Q) != q)
			return false;
		for (auto bit : q)
			if (index.driver(bit) != bank)
				return false;
		FfData ff(&initvals, bank);
		if (ff.has_arst || ff.has_srst || ff.has_aload || ff.has_sr || ff.pol_clk != polarity || index.sigmap(ff.sig_clk) != clock)
			return false;
		data = index.sigmap(ff.sig_d);
		if (ff.has_ce) {
			if (!ff.pol_ce)
				return false;
			enable = index.sigmap(ff.sig_ce)[0];
			return true;
		}
		auto feedback = index.driver(data[0]);
		if (!feedback || feedback->type != ID($mux) || index.port(feedback, ID::Y) != data || index.port(feedback, ID::A) != q)
			return false;
		for (auto bit : data)
			if (index.driver(bit) != feedback)
				return false;
		enable = index.port(feedback, ID::S)[0];
		data = index.port(feedback, ID::B);
		candidates.insert(feedback);
		return true;
	}

	int compress_banks(Cell *mux)
	{
		SigSpec y = index.port(mux, ID::Y), select = index.port(mux, ID::S), banks = index.port(mux, ID::B);
		int width = GetSize(y), branches = GetSize(select);
		if (width == 0 || branches < 2 || branches > 16 || !index.editable(mux))
			return 0;
		auto first = comparison(index, index.driver(select[0]));
		if (!first || first->empty())
			return 0;
		auto state = index.driver(first->begin()->first);
		if (!state || state->type != ID($dff))
			return 0;
		FfData state_ff(&initvals, state);
		SigSpec q = index.sigmap(state_ff.sig_q), d = index.sigmap(state_ff.sig_d), clock = index.sigmap(state_ff.sig_clk);
		if (GetSize(q) > 4 || branches != (1 << GetSize(q)) || !state_ff.val_init.is_fully_def())
			return 0;
		for (auto bit : q)
			if (index.driver(bit) != state)
				return 0;
		pool<unsigned> codes;
		pool<Cell *> candidates{mux, state}, bank_cells;
		SigSpec captured, enables;
		Const initial;
		for (int branch = 0; branch < branches; ++branch) {
			auto decoder = index.driver(select[branch]);
			if (!decoder || decoder->type == ID($ne))
				return 0;
			auto compare = comparison(index, decoder);
			if (!compare || GetSize(*compare) != GetSize(q))
				return 0;
			StateCode capture_code;
			unsigned code = 0;
			bool initial_bank = true;
			for (int offset = 0; offset < GetSize(q); ++offset) {
				auto literal = compare->find(q[offset]);
				if (literal == compare->end())
					return 0;
				bool high = literal->second;
				code |= unsigned(high) << offset;
				initial_bank &= (state_ff.val_init[offset] == State::S1) == high;
				if (d[offset].wire) {
					auto added = capture_code.emplace(d[offset], high);
					if (!added.second && added.first->second != high)
						return 0;
				} else if (d[offset] != (high ? State::S1 : State::S0)) {
					return 0;
				}
			}
			if (!codes.insert(code).second)
				return 0;
			SigSpec bank_q = banks.extract(branch * width, width), data;
			auto bank = index.driver(bank_q[0]);
			SigBit enable;
			if (bank == state || !capture(bank, clock, state_ff.pol_clk, bank_q, data, enable, candidates) || !bank_cells.insert(bank).second)
				return 0;
			auto capture_decoder = index.driver(enable);
			if (!capture_decoder || capture_decoder->type == ID($ne) || comparison(index, capture_decoder) != capture_code)
				return 0;
			candidates.insert(decoder);
			candidates.insert(bank);
			captured.append(data);
			enables.append(enable);
			if (initial_bank)
				initial = initvals(bank_q);
		}
		if (GetSize(initial) != width || !initial.is_fully_def() || !initvals(y).is_fully_undef())
			return 0;
		SigSpec fallback = index.port(mux, ID::A);
		pool<SigBit> inputs, targets(y.begin(), y.end());
		for (const auto *sig : {&captured, &enables, &clock, &fallback})
			inputs.insert(sig->begin(), sig->end());
		if (!index.independent(inputs, targets))
			return 0;
		auto remove = index.removable(candidates, {}, targets, inputs);
		if (!remove.count(mux) || GetSize(remove) <= 2)
			return 0;
		// 每个时钟边沿，下一状态选择的寄存器组同步捕获同一条数据。
		SigSpec output = mux->getPort(ID::Y);
		for (auto cell : remove) {
			if (clocked_ff(cell))
				initvals.remove_init(cell->getPort(ID::Q));
			module->remove(cell);
		}
		auto input = module->addWire(NEW_ID, width);
		module->addPmux(NEW_ID, fallback, captured, enables, input);
		module->addDff(NEW_ID, clock, input, output, state_ff.pol_clk);
		initvals.set_init(output, initial);
		return GetSize(remove) - 2;
	}

public:
	explicit StateWorker(Module *module) : module(module), index(module), initvals(&index.sigmap, module) {}

	void run()
	{
		std::vector<IdString> muxes;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($pmux))
				muxes.push_back(cell->name);
		int groups = 0, saved = 0;
		for (auto name : muxes)
			if (auto mux = module->cell(name)) {
				int delta = compress_banks(mux);
				groups += delta > 0;
				saved += delta;
			}
		if (groups)
			log("  %s: compressed %d synchronous register groups, removed %d net cells.\n", log_id(module), groups, saved);
		replace_decodes();
	}
};

struct OptPmuxStatePass : Pass {
	OptPmuxStatePass() : Pass("opt_pmux_state", "simplify one-hot state and synchronous register groups") {}

	void help() override
	{
		log("    opt_pmux_state [selection]\n\n");
		log("Replace comparisons of provably one-hot registers and combine synchronous\n");
		log("capture banks with complete state selection when RTLIL cell count decreases.\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		log_header(design, "Executing OPT_PMUX_STATE pass.\n");
		if (pmux_coarse_observes_undef(design))
			return;
		for (auto module : design->selected_modules())
			if (module->processes.empty())
				StateWorker(module).run();
	}
} OptPmuxStatePass;

PRIVATE_NAMESPACE_END

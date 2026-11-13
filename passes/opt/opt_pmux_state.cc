#include "kernel/ff.h"
#include "kernel/yosys.h"
#include "passes/opt/pmux_encoding.h"
#include "passes/opt/pmux_rewrite.h"

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

std::optional<StateCode> comparison(PmuxCoarseIndex &index, Cell *cell, pool<SigBit> *dependencies = nullptr)
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
		if (dependencies) {
			if (bit.wire)
				dependencies->insert(bit);
			if (value.wire)
				dependencies->insert(value);
		}
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

int high_literals(const StateCode &code)
{
	return std::count_if(code.begin(), code.end(), [](const auto &literal) { return literal.second; });
}

bool matches_onehot(const StateCode &code, int ones, SigBit high)
{
	auto literal = code.find(high);
	return literal == code.end() ? ones == 0 : literal->second && ones == 1;
}

class StateWorker
{
	Module *module;
	PmuxCoarseIndex index;
	FfInitVals initvals;

	struct OnehotProof {
		bool proven = false;
		pool<SigBit> dependencies;
	};
	using OnehotProofs = dict<Cell *, OnehotProof>;

	std::optional<std::vector<bool>> state_only_branches(const SigSpec &select, const pool<SigBit> &state,
			pool<SigBit> &dependencies)
	{
		std::vector<bool> reachable(GetSize(select) + 1);
		pool<SigBit> matched;
		for (int i = 0; i < GetSize(select); ++i) {
			SigBit bit = select[i];
			if (bit.wire)
				dependencies.insert(bit);
			if (bit == State::S0)
				continue;
			StateCode condition;
			bool inverted = false;
			if (state.count(bit)) {
				condition.emplace(bit, true);
			} else if (bit != State::S1) {
				auto cell = index.driver(bit);
				auto code = comparison(index, cell, &dependencies);
				if (!code || std::any_of(code->begin(), code->end(), [&](const auto &literal) { return !state.count(literal.first); }))
					return std::nullopt;
				condition = std::move(*code);
				inverted = cell->type == ID($ne);
			}
			int ones = high_literals(condition);
			for (auto high : state)
				if (matches_onehot(condition, ones, high) != inverted) {
					if (!matched.insert(high).second)
						return std::nullopt;
					reachable[i + 1] = true;
				}
		}
		reachable[0] = GetSize(matched) < GetSize(state);
		return reachable;
	}

	std::optional<std::vector<bool>> reachable_branches(const SigSpec &select, const pool<SigBit> &state,
			pool<SigBit> &dependencies)
	{
		PmuxEncoding encoding(index, &dependencies);
		std::vector<uint64_t> conditions;
		for (auto bit : select) {
			auto truth = encoding.decode(bit);
			if (!truth)
				return state_only_branches(select, state, dependencies);
			conditions.push_back(*truth);
		}
		unsigned state_mask = 0;
		int state_controls = 0;
		for (int offset = 0; offset < GetSize(encoding.controls); ++offset)
			if (state.count(encoding.controls[offset])) {
				state_mask |= 1u << offset;
				++state_controls;
			}
		std::vector<bool> reachable(GetSize(select) + 1);
		for (unsigned row = 0; row < (1u << GetSize(encoding.controls)); ++row) {
			unsigned state_code = row & state_mask;
			if ((state_code & (state_code - 1)) || (!state_code && state_controls == GetSize(state)))
				continue;
			int branch = 0;
			for (int i = 0; i < GetSize(conditions); ++i)
				if ((conditions[i] >> row) & 1) {
					if (branch)
						return std::nullopt;
					branch = i + 1;
				}
			reachable[branch] = true;
		}
		return reachable;
	}

	bool onehot_next(const SigSpec &value, const pool<SigBit> &bits, pool<Cell *> &active,
			pool<SigSpec> &proven, pool<SigBit> &dependencies, int &budget, int depth)
	{
		if (--budget < 0 || depth > 16 || GetSize(value) != GetSize(bits))
			return false;
		if (proven.count(value))
			return true;
		for (auto bit : value)
			if (bit.wire)
				dependencies.insert(bit);
		if (value.is_fully_const())
			return onehot(value.as_const());
		if (pool<SigBit>(value.begin(), value.end()) == bits)
			return true;
		auto mux = index.driver(value[0]);
		if (!mux || !mux->type.in(ID($mux), ID($pmux)) || index.port(mux, ID::Y) != value || !active.insert(mux).second)
			return false;
		for (auto bit : value)
			if (index.driver(bit) != mux)
				return false;
		SigSpec a = index.port(mux, ID::A), b = index.port(mux, ID::B), select = index.port(mux, ID::S);
		int width = GetSize(value);
		if (GetSize(a) != width || select.empty() || GetSize(select) > 128 || GetSize(b) != width * GetSize(select))
			return false;
		if (mux->type == ID($mux)) {
			if (GetSize(select) != 1 || !onehot_next(a, bits, active, proven, dependencies, budget, depth + 1) ||
					!onehot_next(b, bits, active, proven, dependencies, budget, depth + 1))
				return false;
		} else {
			auto reachable = reachable_branches(select, bits, dependencies);
			if (!reachable || ((*reachable)[0] && !onehot_next(a, bits, active, proven, dependencies, budget, depth + 1)))
				return false;
			for (int branch = 0; branch < GetSize(select); ++branch)
				if ((*reachable)[branch + 1] && !onehot_next(b.extract(branch * width, width), bits, active, proven, dependencies, budget, depth + 1))
					return false;
		}
		active.erase(mux);
		proven.insert(value);
		return true;
	}

	bool onehot_register(Cell *state, pool<SigBit> &dependencies)
	{
		FfData ff(&initvals, state);
		SigSpec q = index.sigmap(ff.sig_q);
		for (auto bit : q)
			if (bit.wire)
				dependencies.insert(bit);
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
		return onehot_next(index.sigmap(ff.sig_d), bits, active, proven, dependencies, budget, 0);
	}

	bool replace_decode(Cell *cell, OnehotProofs &onehot_states)
	{
		if (!index.editable(cell) || !initvals(cell->getPort(ID::Y)).is_fully_undef())
			return false;
		auto compare = comparison(index, cell);
		if (!compare || compare->empty())
			return false;
		auto state = index.driver(compare->begin()->first);
		if (!clocked_ff(state) || std::any_of(compare->begin(), compare->end(), [&](const auto &literal) {
				return index.driver(literal.first) != state;
			}))
			return false;
		auto [status, inserted] = onehot_states.emplace(state, OnehotProof{});
		if (inserted)
			status->second.proven = onehot_register(state, status->second.dependencies);
		if (!status->second.proven)
			return false;

		SigSpec q = index.port(state, ID::Q);
		int required_ones = high_literals(*compare);
		SigBit replacement(State::S0);
		int matches = 0;
		for (auto bit : q) {
			bool equal = matches_onehot(*compare, required_ones, bit);
			if (equal != (cell->type == ID($ne))) {
				matches++;
				replacement = bit;
			}
		}
		if (matches == GetSize(q))
			replacement = State::S1;
		else if (matches > 1)
			return false;

		auto y = index.port(cell, ID::Y);
		auto input = index.sigmap(replacement);
		PmuxRewrite rewrite(module, index, "one-hot state decode");
		rewrite.find_removable({cell}, {}, pool<SigBit>(y.begin(), y.end()), {input});
		rewrite.connect(cell->getPort(ID::Y), input);
		if (!rewrite.validate())
			return false;
		rewrite.commit();
		// 旧输出的驱动已经改变。替代信号保留驱动，只有代表位变化才会影响证明。
		bool input_changed = input.wire && index.sigmap(input) != input;
		for (auto it = onehot_states.begin(); it != onehot_states.end(); ) {
			const auto &dependencies = it->second.dependencies;
			if (dependencies.count(y.as_bit()) || (input_changed && dependencies.count(input)))
				it = onehot_states.erase(it);
			else
				++it;
		}
		return true;
	}

	struct Capture {
		SigSpec data;
		SigBit enable;
		bool active_high;
	};

	std::pair<SigBit, bool> capture_select(const Capture &bank)
	{
		if (bank.active_high)
			return {bank.enable, false};
		auto driver = index.driver(bank.enable);
		if (driver && driver->type.in(ID($not), ID($logic_not)) && GetSize(driver->getPort(ID::A)) == 1 &&
				GetSize(driver->getPort(ID::Y)) == 1)
			return {index.port(driver, ID::A)[0], false};
		return {bank.enable, true};
	}

	std::optional<Capture> capture(Cell *bank, const SigSpec &clock, bool polarity, const SigSpec &q, pool<Cell *> &candidates)
	{
		if (!clocked_ff(bank) || index.port(bank, ID::Q) != q)
			return std::nullopt;
		for (auto bit : q)
			if (index.driver(bit) != bank)
				return std::nullopt;
		FfData ff(&initvals, bank);
		if (ff.has_arst || ff.has_srst || ff.has_aload || ff.has_sr || ff.pol_clk != polarity || index.sigmap(ff.sig_clk) != clock)
			return std::nullopt;
		auto data = index.sigmap(ff.sig_d);
		if (ff.has_ce)
			return Capture{data, index.sigmap(ff.sig_ce)[0], ff.pol_ce};
		auto feedback = index.driver(data[0]);
		if (!feedback || feedback->type != ID($mux) || index.port(feedback, ID::Y) != data)
			return std::nullopt;
		for (auto bit : data)
			if (index.driver(bit) != feedback)
				return std::nullopt;
		auto a = index.port(feedback, ID::A), b = index.port(feedback, ID::B);
		if (a != q && b != q)
			return std::nullopt;
		candidates.insert(feedback);
		return Capture{a == q ? b : a, index.port(feedback, ID::S)[0], a == q};
	}

	SigSpec capture_selection(Module &staging, const std::vector<Capture> &captures, const std::vector<uint64_t> &conditions,
			const SigSpec &fallback, pool<SigBit> &inputs)
	{
		SigSpec data, selects, inverted;
		std::vector<int> invert_offsets;
		for (int code = 0; code < GetSize(captures); ++code) {
			if (!conditions[code])
				continue;
			const auto &bank = captures[code];
			data.append(bank.data);
			inputs.insert(bank.data.begin(), bank.data.end());
			auto [enable, invert] = capture_select(bank);
			if (invert) {
				invert_offsets.push_back(GetSize(selects));
				inverted.append(enable);
			}
			selects.append(enable);
		}
		if (GetSize(selects) == 1)
			return data;
		inputs.insert(fallback.begin(), fallback.end());
		inputs.insert(selects.begin(), selects.end());
		if (!inverted.empty()) {
			auto normalized = staging.addWire(NEW_ID, GetSize(inverted));
			staging.addNot(NEW_ID, inverted, normalized);
			for (int i = 0; i < GetSize(invert_offsets); ++i)
				selects[invert_offsets[i]] = SigBit(normalized, i);
		}
		auto output = staging.addWire(NEW_ID, GetSize(fallback));
		staging.addPmux(NEW_ID, fallback, data, selects, output);
		return output;
	}

	SigSpec encoded_selection(Module &staging, const std::vector<Capture> &captures, const std::vector<uint64_t> &conditions,
			const std::vector<SigBit> &controls, int width, pool<SigBit> &inputs)
	{
		std::vector<SigSpec> rows(1 << GetSize(controls));
		for (int code = 0; code < GetSize(captures); ++code)
			for (int row = 0; row < GetSize(rows); ++row)
				if ((conditions[code] >> row) & 1) {
					rows[row] = captures[code].data;
					inputs.insert(rows[row].begin(), rows[row].end());
				}
		for (auto control : controls) {
			SigSpec low, high;
			std::vector<int> offsets;
			for (int row = 0; row < GetSize(rows) / 2; ++row) {
				if (rows[2 * row] == rows[2 * row + 1]) {
					rows[row] = rows[2 * row];
					continue;
				}
				low.append(rows[2 * row]);
				high.append(rows[2 * row + 1]);
				offsets.push_back(row);
			}
			rows.resize(GetSize(rows) / 2);
			if (!offsets.empty()) {
				inputs.insert(control);
				SigSpec stage = staging.addWire(NEW_ID, GetSize(low));
				staging.addMux(NEW_ID, low, high, control, stage);
				for (int i = 0; i < GetSize(offsets); ++i)
					rows[offsets[i]] = stage.extract(i * width, width);
			}
		}
		return rows.front();
	}

	bool compress_bank_group(Cell *mux)
	{
		if (!pmux_select_shape(mux) || !index.editable(mux))
			return false;
		SigSpec y = index.port(mux, ID::Y), select = index.port(mux, ID::S), banks = index.port(mux, ID::B);
		int width = GetSize(y), branches = GetSize(select);
		if (branches < 2 || branches > 16 || !initvals(y).is_fully_undef())
			return false;
		PmuxEncoding output_encoding(index);
		std::vector<int> selected_banks;
		if (!output_encoding.branch_table(select, selected_banks) || GetSize(selected_banks) != branches ||
				output_encoding.controls.empty())
			return false;
		auto state = index.driver(output_encoding.controls.front());
		if (!state || state->type != ID($dff))
			return false;
		FfData state_ff(&initvals, state);
		SigSpec q = index.sigmap(state_ff.sig_q), d = index.sigmap(state_ff.sig_d), clock = index.sigmap(state_ff.sig_clk);
		if (GetSize(q) != GetSize(output_encoding.controls) || !state_ff.val_init.is_fully_def())
			return false;
		PmuxEncoding capture_encoding(index);
		std::vector<uint64_t> next_bits;
		for (auto bit : q)
			if (index.driver(bit) != state || !output_encoding.slots.count(bit))
				return false;
		for (auto bit : d) {
			auto truth = capture_encoding.pin(bit);
			if (!truth)
				return false;
			next_bits.push_back(*truth);
		}
		int capture_controls = GetSize(capture_encoding.controls);
		pool<int> seen_banks;
		pool<Cell *> candidates = output_encoding.cells, bank_cells;
		candidates.insert(mux);
		candidates.insert(state);
		std::vector<Capture> captures(branches);
		std::vector<uint64_t> conditions(branches);
		Const initial;
		for (int row = 0; row < branches; ++row) {
			int branch = selected_banks[row];
			if (branch < 0 || !seen_banks.insert(branch).second)
				return false;
			unsigned code = 0;
			uint64_t condition = ~uint64_t(0);
			bool initial_bank = true;
			for (int offset = 0; offset < GetSize(q); ++offset) {
				bool high = (row >> output_encoding.slots.at(q[offset])) & 1;
				code |= unsigned(high) << offset;
				initial_bank &= (state_ff.val_init[offset] == State::S1) == high;
				condition &= high ? next_bits[offset] : ~next_bits[offset];
			}
			SigSpec bank_q = banks.extract(branch * width, width);
			auto bank = index.driver(bank_q[0]);
			auto bank_capture = capture(bank, clock, state_ff.pol_clk, bank_q, candidates);
			if (bank == state || !bank_capture || !bank_cells.insert(bank).second)
				return false;
			auto truth = capture_encoding.decode(bank_capture->enable);
			if (!truth || GetSize(capture_encoding.controls) != capture_controls || (bank_capture->active_high ? *truth : ~*truth) != condition)
				return false;
			candidates.insert(bank);
			captures[code] = std::move(*bank_capture);
			conditions[code] = condition;
			if (initial_bank)
				initial = initvals(bank_q);
		}
		if (GetSize(initial) != width || !initial.is_fully_def())
			return false;
		candidates.insert(capture_encoding.cells.begin(), capture_encoding.cells.end());
		SigSpec output = mux->getPort(ID::Y);
		pool<SigBit> targets(y.begin(), y.end());
		pool<SigBit> encoded_inputs(clock.begin(), clock.end());
		encoded_inputs.insert(capture_encoding.controls.begin(), capture_encoding.controls.end());
		for (int code = 0; code < GetSize(captures); ++code)
			if (conditions[code])
				encoded_inputs.insert(captures[code].data.begin(), captures[code].data.end());
		auto private_cells = index.removable(candidates, {}, targets, encoded_inputs);
		bool reuse_decode = false;
		for (int code = 0; code < GetSize(captures); ++code) {
			if (!conditions[code])
				continue;
			auto [enable, invert] = capture_select(captures[code]);
			auto driver = index.driver(enable);
			if (!invert && driver && capture_encoding.cells.count(driver) && !private_cells.count(driver)) {
				reuse_decode = true;
				break;
			}
		}
		for (bool encoded : {!reuse_decode, reuse_decode}) {
			PmuxRewrite rewrite(module, index, encoded ? "encoded synchronous capture" : "decoded synchronous capture");
			pool<SigBit> inputs(clock.begin(), clock.end());
			SigSpec input = encoded ? encoded_selection(rewrite.staging, captures, conditions, capture_encoding.controls, width, inputs) :
				capture_selection(rewrite.staging, captures, conditions, index.port(mux, ID::A), inputs);
			if (!index.independent(inputs, targets))
				continue;
			rewrite.staging.addDff(NEW_ID, clock, input, output, state_ff.pol_clk, mux->get_src_attribute());
			rewrite.find_removable(candidates, {}, targets, inputs);
			int removed_bits = 0;
			for (auto cell : rewrite.removed)
				if (clocked_ff(cell))
					removed_bits += GetSize(cell->getPort(ID::Q));
			if (!rewrite.removed.count(mux) || removed_bits <= width || !rewrite.validate())
				continue;
			for (auto cell : rewrite.removed)
				if (clocked_ff(cell))
					initvals.remove_init(cell->getPort(ID::Q));
			rewrite.commit();
			initvals.set_init(output, initial);
			return true;
		}
		return false;
	}

public:
	explicit StateWorker(Module *module) : module(module), index(module), initvals(&index.sigmap, module) {}

	int compress_banks()
	{
		std::vector<IdString> muxes;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($pmux))
				muxes.push_back(cell->name);
		int groups = 0;
		for (auto name : muxes)
			if (auto mux = module->cell(name); mux && mux->type == ID($pmux))
				groups += compress_bank_group(mux);
		return groups;
	}

	int replace_decodes()
	{
		std::vector<IdString> decodes;
		for (auto cell : module->selected_cells())
			if (cell->type.in(ID($eq), ID($ne), ID($logic_not)))
				decodes.push_back(cell->name);
		OnehotProofs onehot_states;
		int removed = 0;
		for (auto name : decodes) {
			auto cell = module->cell(name);
			if (!cell || !replace_decode(cell, onehot_states))
				continue;
			++removed;
		}
		return removed;
	}
};

struct OptPmuxStatePass : Pass {
	OptPmuxStatePass() : Pass("opt_pmux_state", "simplify one-hot state and synchronous register groups") {}

	void help() override
	{
		log("    opt_pmux_state [selection]\n\n");
		log("Replace comparisons of provably one-hot registers and combine synchronous\n");
		log("capture banks with complete state selection when fewer register bits suffice.\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		log_header(design, "Executing OPT_PMUX_STATE pass.\n");
		if (pmux_coarse_observes_undef(design))
			return;
		for (auto module : design->selected_modules()) {
			if (!module->processes.empty())
				continue;
			StateWorker worker(module);
			int before = module->cells_size();
			int groups = worker.compress_banks();
			if (groups)
				log("  %s: compressed %d synchronous register groups (net RTLIL cell change: %+d).\n", log_id(module), groups, module->cells_size() - before);
			int decodes = worker.replace_decodes();
			if (decodes)
				log("  %s: removed %d one-hot state decoders.\n", log_id(module), decodes);
		}
	}
} OptPmuxStatePass;

PRIVATE_NAMESPACE_END

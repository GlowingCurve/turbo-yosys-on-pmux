#include "kernel/ff.h"
#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

#include <bit>
#include <numeric>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct StateCode {
	pool<SigBit> zeros, ones;
	bool inverted = false;

	bool matches(SigBit high) const
	{
		bool equal = ones.empty() ? !zeros.count(high) : GetSize(ones) == 1 && ones.count(high);
		return equal != inverted;
	}

	bool uses_only(const pool<SigBit> &state) const
	{
		auto contains = [&](SigBit bit) { return state.count(bit); };
		return std::all_of(zeros.begin(), zeros.end(), contains) && std::all_of(ones.begin(), ones.end(), contains);
	}
};

std::optional<StateCode> comparison_literals(const SigMap &sigmap, Cell *cell)
{
	if (!cell || !cell->type.in(ID($eq), ID($ne), ID($logic_not)) || GetSize(cell->getPort(ID::Y)) != 1)
		return std::nullopt;
	auto operands = pmux_comparison_operands(cell, 128, sigmap);
	if (!operands)
		return std::nullopt;
	const auto &[a, b] = *operands;
	StateCode result{{}, {}, cell->type == ID($ne)};
	for (int offset = 0; offset < GetSize(a); ++offset) {
		SigBit bit = a[offset], value = b[offset];
		if (!bit.wire)
			std::swap(bit, value);
		if (value != State::S0 && value != State::S1)
			return std::nullopt;
		if (bit == value)
			continue;
		bool high = value == State::S1;
		if (!bit.wire || (high ? result.zeros : result.ones).count(bit))
			return std::nullopt;
		(high ? result.ones : result.zeros).insert(bit);
	}
	return result;
}

class StateWorker
{
	Module *module;
	PmuxCoarseIndex index;
	FfInitVals initvals;

	std::optional<std::vector<bool>> reachable_branches(const SigSpec &select, const pool<SigBit> &state)
	{
		PmuxEncoding encoding(index);
		std::vector<uint64_t> conditions;
		for (auto bit : select) {
			auto truth = encoding.decode(bit);
			if (!truth)
				break;
			conditions.push_back(*truth);
		}
		std::vector<bool> reachable(GetSize(select) + 1);
		if (GetSize(conditions) != GetSize(select)) {
			// Wide state vectors can still be proved with state-only comparisons.
			std::vector<StateCode> codes;
			for (auto bit : select) {
				auto code = state.count(bit) ? StateCode{{}, {bit}} : bit == State::S0 ? StateCode{{}, {}, true} :
						bit == State::S1 ? std::optional<StateCode>(StateCode{}) : comparison_literals(index.sigmap, index.driver(bit));
				if (!code || !code->uses_only(state))
					return std::nullopt;
				codes.push_back(std::move(*code));
			}
			for (auto high : state) {
				int arm = 0;
				for (int i = 0; i < GetSize(codes); ++i)
					if (codes[i].matches(high)) {
						if (arm)
							return std::nullopt;
						arm = i + 1;
					}
				reachable[arm] = true;
			}
			return reachable;
		}
		unsigned state_mask = 0;
		for (int offset = 0; offset < GetSize(encoding.controls()); ++offset)
			if (state.count(encoding.controls()[offset]))
				state_mask |= 1u << offset;
		bool full_state = std::popcount(state_mask) == GetSize(state);
		int controls = GetSize(encoding.controls());
		uint64_t valid = 0;
		for (int row = 0; row < pmux_encoding_limit(controls); ++row) {
			int ones = std::popcount(unsigned(row) & state_mask);
			if (ones == 1 || (ones == 0 && !full_state))
				valid |= uint64_t(1) << row;
		}
		auto table = pmux_branch_table(conditions, controls, valid);
		if (!table)
			return std::nullopt;
		for (; valid; valid &= valid - 1)
			reachable[(*table)[std::countr_zero(valid)]] = true;
		return reachable;
	}

	static bool onehot(const Const &value)
	{
		return value.is_fully_def() && std::count(value.begin(), value.end(), State::S1) == 1;
	}

	bool onehot_next(const SigSpec &value, const pool<SigBit> &bits, dict<SigSpec, bool> &proven, int &budget, int depth)
	{
		if (budget == 0 || depth > 16 || GetSize(value) != GetSize(bits))
			return false;
		--budget;
		if (value.is_fully_const())
			return onehot(value.as_const());
		if (value.to_sigbit_pool() == bits)
			return true;
		if (auto [proof, inserted] = proven.emplace(value, false); !inserted)
			return proof->second;
		auto mux = index.driver(value[0]);
		if (!mux || !mux->type.in(ID($mux), ID($pmux)) || index.port(mux, ID::Y) != value)
			return false;
		for (auto bit : value)
			if (index.driver(bit) != mux)
				return false;
		auto a = index.port(mux, ID::A), b = index.port(mux, ID::B), select = index.port(mux, ID::S);
		int width = GetSize(value), branches = GetSize(select);
		log_assert(GetSize(a) == width && branches > 0 && GetSize(b) == width * branches);
		if (branches > 128)
			return false;
		const auto reachable = mux->type == ID($pmux) ? reachable_branches(select, bits) : std::vector<bool>{true, true};
		if (!reachable)
			return false;
		log_assert(GetSize(*reachable) == GetSize(select) + 1);
		a.append(b);
		for (int branch = 0; branch <= branches; ++branch)
			if ((*reachable)[branch] && !onehot_next(a.extract(branch * width, width), bits, proven, budget, depth + 1))
				return false;
		return proven.at(value) = true;
	}

	bool onehot_register(Cell *state, const pool<SigBit> &bits)
	{
		FfData ff(&initvals, state);
		if (ff.has_aload || ff.has_sr || GetSize(bits) != ff.width || ff.width < 2 || ff.width > 128 || !onehot(ff.val_init) ||
				(ff.has_arst && !onehot(ff.val_arst)) || (ff.has_srst && !onehot(ff.val_srst)))
			return false;
		if (std::any_of(bits.begin(), bits.end(), [&](SigBit bit) { return index.driver(bit) != state; }))
			return false;
		dict<SigSpec, bool> proven;
		int budget = 128;
		return onehot_next(index.sigmap(ff.sig_d), bits, proven, budget, 0);
	}

	bool replace_decode(Cell *cell, dict<Cell *, bool> &onehot_states)
	{
		if (!index.editable(cell) || !initvals(cell->getPort(ID::Y)).is_fully_undef())
			return false;
		auto compare = comparison_literals(index.sigmap, cell);
		if (!compare || (compare->zeros.empty() && compare->ones.empty()))
			return false;
		const auto &literals = compare->ones.empty() ? compare->zeros : compare->ones;
		auto state = index.driver(*literals.begin());
		if (!state || !pmux_is_clocked_ff(state))
			return false;
		SigSpec q = index.port(state, ID::Q);
		auto state_bits = q.to_sigbit_pool();
		if (!compare->uses_only(state_bits))
			return false;
		auto [proof, inserted] = onehot_states.emplace(state, false);
		if (inserted)
			proof->second = onehot_register(state, state_bits);
		if (!proof->second)
			return false;
		SigBit replacement(State::S0);
		int matches = 0;
		for (auto bit : q)
			if (compare->matches(bit)) {
				matches++;
				replacement = bit;
			}
		if (matches > 1 && matches != GetSize(q))
			return false;
		PmuxRewrite rewrite(module, index, "onehot_state_decode");
		rewrite.connect(cell->getPort(ID::Y), matches == GetSize(q) ? SigBit(State::S1) : replacement);
		rewrite.find_removable({cell});
		if (!rewrite.validate())
			return false;
		rewrite.commit();
		return true;
	}

	struct Capture {
		SigSpec data;
		SigBit enable;
		bool active_high;
	};
	struct CaptureGroup {
		std::vector<Capture> banks;
		const PmuxEncoding &encoding;
		std::vector<int> arms;
		pool<Cell *> candidates;
		SigSpec clock;
		Const initial;
		bool polarity;
	};

	std::optional<Capture> capture(Cell *bank, const SigSpec &clock, bool polarity, const SigSpec &q, pool<Cell *> &candidates)
	{
		if (!bank || !pmux_is_clocked_ff(bank) || index.port(bank, ID::Q) != q)
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

	SigSpec decoded_input(Module &staging, const std::vector<Capture> &banks, const SigSpec &fallback)
	{
		SigSpec data, selects, inverted;
		std::vector<int> invert_offsets;
		for (const auto &bank : banks) {
			if (bank.data.empty())
				continue;
			data.append(bank.data);
			auto enable = bank.enable;
			auto inverter = bank.active_high ? nullptr : index.driver(enable);
			if (inverter && inverter->type.in(ID($not), ID($logic_not)) &&
					GetSize(inverter->getPort(ID::A)) == 1 && GetSize(inverter->getPort(ID::Y)) == 1) {
				enable = index.port(inverter, ID::A).as_bit();
			} else if (!bank.active_high) {
				invert_offsets.push_back(GetSize(selects));
				inverted.append(enable);
			}
			selects.append(enable);
		}
		if (GetSize(selects) == 1)
			return data;
		if (!inverted.empty()) {
			auto normalized = staging.Not(NEW_ID, inverted);
			for (int i = 0; i < GetSize(invert_offsets); ++i)
				selects[invert_offsets[i]] = normalized[i];
		}
		return staging.Pmux(NEW_ID, fallback, data, selects);
	}

	SigSpec encoded_input(Module &staging, const CaptureGroup &group, int width)
	{
		PmuxSelectTree tree(index, group.encoding);
		std::vector<int> controls(GetSize(group.encoding.controls())), roots, rows(group.arms.size());
		std::iota(controls.begin(), controls.end(), 0);
		for (int bit = 0; bit < width; ++bit) {
			for (int row = 0; row < GetSize(rows); ++row)
				rows[row] = tree.literal(group.banks[group.arms[row] - 1].data[bit]);
			roots.push_back(tree.column(rows, controls));
		}
		return tree.emit(&staging, roots, {}, tree.analyze(roots));
	}

	std::optional<CaptureGroup> analyze_banks(Cell *mux, PmuxEncoding &capture_encoding)
	{
		SigSpec y = index.port(mux, ID::Y), select = index.port(mux, ID::S), banks = index.port(mux, ID::B);
		int width = GetSize(y), branches = GetSize(select);
		if (branches < 2 || branches > 16 || !initvals(y).is_fully_undef())
			return std::nullopt;
		PmuxEncoding output_encoding(index);
		std::vector<int> selected_banks;
		if (!output_encoding.branch_table(select, selected_banks) || GetSize(selected_banks) != branches ||
				output_encoding.controls().empty())
			return std::nullopt;
		auto state = index.driver(output_encoding.controls().front());
		if (!state || state->type != ID($dff))
			return std::nullopt;
		FfData state_ff(&initvals, state);
		SigSpec q = index.sigmap(state_ff.sig_q);
		if (GetSize(q) != GetSize(output_encoding.controls()) || !state_ff.val_init.is_fully_def())
			return std::nullopt;
		CaptureGroup group{std::vector<Capture>(branches), capture_encoding, {}, output_encoding.cells(),
				index.sigmap(state_ff.sig_clk), {}, state_ff.pol_clk};
		group.candidates.insert(mux);
		group.candidates.insert(state);
		std::vector<uint64_t> next_bits;
		for (auto bit : q)
			if (index.driver(bit) != state || !output_encoding.slots().count(bit))
				return std::nullopt;
		for (auto bit : index.sigmap(state_ff.sig_d)) {
			auto truth = capture_encoding.pin(bit);
			if (!truth)
				return std::nullopt;
			next_bits.push_back(*truth);
		}
		const int control_count = GetSize(capture_encoding.controls());
		pool<int> seen_banks;
		pool<Cell *> seen_cells{state};
		std::vector<uint64_t> conditions(branches);
		const unsigned initial_code = state_ff.val_init.as_int();
		for (unsigned row = 0; row < unsigned(branches); ++row) {
			const int arm = selected_banks[row];
			if (arm == 0 || !seen_banks.insert(arm).second)
				return std::nullopt;
			unsigned code = 0;
			uint64_t condition = ~uint64_t(0);
			for (int offset = 0; offset < GetSize(q); ++offset) {
				bool high = (row >> output_encoding.slots().at(q[offset])) & 1;
				code |= unsigned(high) << offset;
				condition &= high ? next_bits[offset] : ~next_bits[offset];
			}
			SigSpec bank_q = banks.extract((arm - 1) * width, width);
			auto bank = index.driver(bank_q[0]);
			auto next = capture(bank, group.clock, group.polarity, bank_q, group.candidates);
			if (!next || !seen_cells.insert(bank).second)
				return std::nullopt;
			auto truth = capture_encoding.decode(next->enable);
			if (!truth || GetSize(capture_encoding.controls()) != control_count || (next->active_high ? *truth : ~*truth) != condition)
				return std::nullopt;
			group.candidates.insert(bank);
			conditions[code] = condition;
			if (condition)
				group.banks[code] = std::move(*next);
			if (code == initial_code)
				group.initial = initvals(bank_q);
		}
		if (GetSize(group.initial) != width || !group.initial.is_fully_def())
			return std::nullopt;
		auto table = pmux_branch_table(conditions, control_count);
		log_assert(table && std::none_of(table->begin(), table->end(), [](int arm) { return arm == 0; }));
		group.arms = std::move(*table);
		group.candidates.insert(capture_encoding.cells().begin(), capture_encoding.cells().end());
		return group;
	}

	bool compress_bank_group(Cell *mux)
	{
		if (!pmux_select_shape(mux) || !index.editable(mux))
			return false;
		PmuxEncoding encoding(index);
		auto group = analyze_banks(mux, encoding);
		if (!group)
			return false;
		const SigSpec output = mux->getPort(ID::Y);
		std::unique_ptr<PmuxRewrite> best;
		std::pair<int, int> best_gain{};
		for (bool reuse_decode : {false, true}) {
			auto candidate = std::make_unique<PmuxRewrite>(module, index,
					reuse_decode ? "decoded_sync_capture" : "encoded_sync_capture");
			auto &staging = candidate->staging;
			const auto data = reuse_decode ? decoded_input(staging, group->banks, index.port(mux, ID::A)) :
					encoded_input(staging, *group, GetSize(output));
			staging.addDff(NEW_ID, group->clock, data, output, group->polarity, mux->get_src_attribute());
			candidate->find_removable(group->candidates);
			int saved_bits = -GetSize(output);
			for (auto cell : candidate->removed)
				if (pmux_is_clocked_ff(cell))
					saved_bits += GetSize(cell->getPort(ID::Q));
			const std::pair gain{saved_bits, GetSize(candidate->removed) - candidate->added_count()};
			if (saved_bits > 0 && gain > best_gain && candidate->removed.count(mux) && candidate->validate()) {
				best_gain = gain;
				best = std::move(candidate);
			}
		}
		if (!best)
			return false;
		for (auto cell : best->removed)
			if (pmux_is_clocked_ff(cell))
				initvals.remove_init(cell->getPort(ID::Q));
		best->commit();
		initvals.set_init(output, group->initial);
		return true;
	}

public:
	explicit StateWorker(Module *module) : module(module), index(module), initvals(&index.sigmap, module) {}

	int run()
	{
		std::vector<IdString> muxes, decodes;
		for (auto cell : module->selected_cells())
			if (cell->type == ID($pmux))
				muxes.push_back(cell->name);
			else if (cell->type.in(ID($eq), ID($ne), ID($logic_not)))
				decodes.push_back(cell->name);
		int changes = 0;
		for (auto name : muxes)
			if (auto mux = module->cell(name))
				changes += compress_bank_group(mux);
		dict<Cell *, bool> onehot_states;
		for (auto name : decodes)
			if (auto cell = module->cell(name))
				changes += replace_decode(cell, onehot_states);
		return changes;
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
		pmux_run_pass(design, "opt_pmux_state", "Executing OPT_PMUX_STATE pass.\n",
				[](Module *module) { return StateWorker(module).run(); });
	}
} OptPmuxStatePass;

PRIVATE_NAMESPACE_END

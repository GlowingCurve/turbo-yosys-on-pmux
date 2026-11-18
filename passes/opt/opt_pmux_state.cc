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

// 优化方法层的状态与寄存器化简。合并按状态采样的寄存器，并用状态位替换 one-hot 比较器。

#include "kernel/ff.h"
#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

#include <bit>
#include <numeric>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 用状态位的零值和一值约束表示一个分支条件。
struct StateCode {
	pool<SigBit> zeros, ones;
	bool inverted = false;

	// 判断指定状态位独占高电平时条件是否成立。
	bool matches(SigBit high) const
	{
		bool equal = ones.empty() ? !zeros.count(high) : GetSize(ones) == 1 && ones.count(high);
		return equal != inverted;
	}

	// 确认分支条件只依赖目标状态寄存器。
	bool uses_only(const pool<SigBit> &state) const
	{
		auto contains = [&](SigBit bit) { return state.count(bit); };
		return std::all_of(zeros.begin(), zeros.end(), contains) && std::all_of(ones.begin(), ones.end(), contains);
	}
};

// 从比较器提取可由状态位直接表示的条件。
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

// 解析状态位、常量或由比较器产生的单比特条件。
std::optional<StateCode> state_code(PmuxCoarseIndex &index, SigBit bit, const pool<SigBit> &state)
{
	if (state.count(bit))
		return StateCode{{}, {bit}};
	if (bit == State::S0)
		return StateCode{{}, {}, true};
	if (bit == State::S1)
		return StateCode{};
	return comparison_literals(index.sigmap, index.driver(bit));
}

// 列出 one-hot 约束允许进入的选择分支。
std::optional<std::vector<bool>> reachable_branches(PmuxCoarseIndex &index, const SigSpec &select, const pool<SigBit> &state)
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
		// 状态位较多时，直接检查只依赖状态位的比较条件。
		std::vector<StateCode> codes;
		for (auto bit : select) {
			auto code = state_code(index, bit, state);
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

// 检查常量中是否恰好有一个确定的高电平。
static bool onehot(const Const &value) { return value.is_fully_def() && std::count(value.begin(), value.end(), State::S1) == 1; }

// 递归检查所有可达次态分支是否保持 one-hot。
bool onehot_next(PmuxCoarseIndex &index, const SigSpec &value, const pool<SigBit> &bits, dict<SigSpec, bool> &proven, int &budget, int depth)
{
	if (budget == 0 || depth > 16 || GetSize(value) != GetSize(bits))
		return false;
	--budget;
	if (value.is_fully_const())
		return onehot(value.as_const());
	if (value.to_sigbit_pool() == bits)
		return true;
	auto [proof, inserted] = proven.emplace(value, false);
	if (!inserted)
		return proof->second;
	auto mux = index.driver(value[0]);
	if (!mux || !mux->type.in(ID($mux), ID($pmux)) || index.port(mux, ID::Y) != value)
		return false;
	for (auto bit : value)
		if (index.driver(bit) != mux)
			return false;
	auto a = index.port(mux, ID::A);
	auto b = index.port(mux, ID::B);
	auto select = index.port(mux, ID::S);
	int width = GetSize(value);
	int branches = GetSize(select);
	log_assert(GetSize(a) == width && branches > 0 && GetSize(b) == width * branches);
	if (branches > 128)
		return false;
	const auto reachable = mux->type == ID($pmux) ? reachable_branches(index, select, bits) : std::vector<bool>{true, true};
	if (!reachable)
		return false;
	log_assert(GetSize(*reachable) == GetSize(select) + 1);
	a.append(b);
	for (int branch = 0; branch <= branches; ++branch)
		if ((*reachable)[branch] && !onehot_next(index, a.extract(branch * width, width), bits, proven, budget, depth + 1))
			return false;
	proven.at(value) = true;
	return true;
}

// 检查状态寄存器的初值、复位值及次态输入。
bool onehot_register(PmuxCoarseIndex &index, FfInitVals &initvals, Cell *state, const pool<SigBit> &bits)
{
	FfData ff(&initvals, state);
	if (ff.has_aload || ff.has_sr || GetSize(bits) != ff.width || ff.width < 2 || ff.width > 128 || !onehot(ff.val_init) ||
	    (ff.has_arst && !onehot(ff.val_arst)) || (ff.has_srst && !onehot(ff.val_srst)))
		return false;
	if (std::any_of(bits.begin(), bits.end(), [&](SigBit bit) { return index.driver(bit) != state; }))
		return false;
	dict<SigSpec, bool> proven;
	int budget = 128;
	return onehot_next(index, index.sigmap(ff.sig_d), bits, proven, budget, 0);
}

// 将比较器替换为等价的状态位或常量。
bool replace_decode(PmuxCoarseIndex &index, FfInitVals &initvals, Cell *cell, dict<Cell *, bool> &onehot_states)
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
		proof->second = onehot_register(index, initvals, state, state_bits);
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
	PmuxRewrite rewrite(index.module, index, "onehot_state_decode");
	rewrite.connect(cell->getPort(ID::Y), matches == GetSize(q) ? SigBit(State::S1) : replacement);
	rewrite.find_removable({cell});
	if (!rewrite.validate())
		return false;
	rewrite.commit();
	return true;
}

// 描述一组同步采样的数据输入和写使能极性。
struct Capture {
	SigSpec data;
	SigBit enable;
	bool active_high;
};
// 保存各状态下的采样寄存器及共同的时钟和初始值。
struct CaptureGroup {
	std::vector<Capture> banks;
	PmuxEncoding encoding;
	std::vector<int> arms;
	pool<Cell *> candidates;
	SigSpec clock;
	Const initial;
	bool polarity;
};

// 识别显式使能或反馈选择器控制的同步采样。
std::optional<Capture> capture(PmuxCoarseIndex &index, FfInitVals &initvals, Cell *bank, const SigSpec &clock, bool polarity, const SigSpec &q,
			       pool<Cell *> &candidates)
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
	auto a = index.port(feedback, ID::A);
	auto b = index.port(feedback, ID::B);
	if (a != q && b != q)
		return std::nullopt;
	candidates.insert(feedback);
	return Capture{a == q ? b : a, index.port(feedback, ID::S)[0], a == q};
}

// 复用现有译码信号构造寄存器的数据输入。
SigSpec decoded_input(PmuxCoarseIndex &index, Module &staging, const std::vector<Capture> &banks, const SigSpec &fallback)
{
	SigSpec data, selects, inverted;
	std::vector<int> invert_offsets;
	for (const auto &bank : banks) {
		if (bank.data.empty())
			continue;
		data.append(bank.data);
		auto enable = bank.enable;
		auto inverter = bank.active_high ? nullptr : index.driver(enable);
		if (inverter && inverter->type.in(ID($not), ID($logic_not)) && GetSize(inverter->getPort(ID::A)) == 1 &&
		    GetSize(inverter->getPort(ID::Y)) == 1) {
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

// 按编码行构造采样寄存器之前的选择树。
SigSpec encoded_input(PmuxCoarseIndex &index, Module &staging, const CaptureGroup &group, int width)
{
	PmuxSelectTree tree(index, group.encoding);
	std::vector<int> controls(GetSize(group.encoding.controls()));
	std::vector<int> roots;
	std::vector<int> rows(group.arms.size());
	std::iota(controls.begin(), controls.end(), 0);
	for (int bit = 0; bit < width; ++bit) {
		for (int row = 0; row < GetSize(rows); ++row)
			rows[row] = tree.literal(group.banks[group.arms[row] - 1].data[bit]);
		roots.push_back(tree.column(rows, controls));
	}
	return tree.emit(&staging, roots, {}, tree.analyze(roots));
}

// 检查各组寄存器的使能条件，并取得电路上电时所选分支的初始值。
bool verify_capture_banks(PmuxCoarseIndex &index, FfInitVals &initvals, CaptureGroup &group, Cell *state, const SigSpec &q, const SigSpec &banks,
			  const PmuxEncoding &output_encoding, const std::vector<int> &selected_banks, const std::vector<uint64_t> &next_bits,
			  int width, unsigned initial_code)
{
	auto &capture_encoding = group.encoding;
	int branches = GetSize(selected_banks);
	const int control_count = GetSize(capture_encoding.controls());
	pool<int> seen_banks;
	pool<Cell *> seen_cells{state};
	std::vector<uint64_t> conditions(branches);
	for (unsigned row = 0; row < unsigned(branches); ++row) {
		const int arm = selected_banks[row];
		if (arm == 0 || !seen_banks.insert(arm).second)
			return false;
		unsigned code = 0;
		uint64_t condition = ~uint64_t(0);
		for (int offset = 0; offset < GetSize(q); ++offset) {
			bool high = (row >> output_encoding.slots().at(q[offset])) & 1;
			code |= unsigned(high) << offset;
			condition &= high ? next_bits[offset] : ~next_bits[offset];
		}
		SigSpec bank_q = banks.extract((arm - 1) * width, width);
		auto bank = index.driver(bank_q[0]);
		auto next = capture(index, initvals, bank, group.clock, group.polarity, bank_q, group.candidates);
		if (!next || !seen_cells.insert(bank).second)
			return false;
		auto truth = capture_encoding.decode(next->enable);
		if (!truth || GetSize(capture_encoding.controls()) != control_count || (next->active_high ? *truth : ~*truth) != condition)
			return false;
		group.candidates.insert(bank);
		conditions[code] = condition;
		if (condition)
			group.banks[code] = std::move(*next);
		if (code == initial_code)
			group.initial = initvals(bank_q);
	}
	if (GetSize(group.initial) != width || !group.initial.is_fully_def())
		return false;
	auto table = pmux_branch_table(conditions, control_count);
	log_assert(table && std::none_of(table->begin(), table->end(), [](int arm) { return arm == 0; }));
	group.arms = std::move(*table);
	group.candidates.insert(capture_encoding.cells().begin(), capture_encoding.cells().end());
	return true;
}

// 确定状态寄存器和输出分支的对应关系，再检查各组采样寄存器。
std::optional<CaptureGroup> analyze_banks(PmuxCoarseIndex &index, FfInitVals &initvals, Cell *mux)
{
	SigSpec y = index.port(mux, ID::Y);
	SigSpec select = index.port(mux, ID::S);
	SigSpec banks = index.port(mux, ID::B);
	int width = GetSize(y);
	int branches = GetSize(select);
	if (branches < 2 || branches > 16 || !initvals(y).is_fully_undef())
		return std::nullopt;
	PmuxEncoding output_encoding(index);
	std::vector<int> selected_banks;
	if (!output_encoding.branch_table(select, selected_banks) || GetSize(selected_banks) != branches || output_encoding.controls().empty())
		return std::nullopt;
	auto state = index.driver(output_encoding.controls().front());
	if (!state || state->type != ID($dff))
		return std::nullopt;
	FfData state_ff(&initvals, state);
	SigSpec q = index.sigmap(state_ff.sig_q);
	if (GetSize(q) != GetSize(output_encoding.controls()) || !state_ff.val_init.is_fully_def())
		return std::nullopt;
	CaptureGroup group{
	  std::vector<Capture>(branches), PmuxEncoding(index), {}, output_encoding.cells(), index.sigmap(state_ff.sig_clk), {}, state_ff.pol_clk};
	auto &capture_encoding = group.encoding;
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
	if (!verify_capture_banks(index, initvals, group, state, q, banks, output_encoding, selected_banks, next_bits, width,
				  state_ff.val_init.as_int()))
		return std::nullopt;
	return group;
}

// 比较复用译码和重建选择树的收益，提交较好的方案。
bool compress_bank_group(PmuxCoarseIndex &index, FfInitVals &initvals, Cell *mux)
{
	if (!pmux_select_shape(mux) || !index.editable(mux))
		return false;
	auto group = analyze_banks(index, initvals, mux);
	if (!group)
		return false;
	const SigSpec output = mux->getPort(ID::Y);
	std::unique_ptr<PmuxRewrite> best;
	std::pair<int, int> best_gain{};
	for (bool reuse_decode : {false, true}) {
		auto candidate = std::make_unique<PmuxRewrite>(index.module, index, reuse_decode ? "decoded_sync_capture" : "encoded_sync_capture");
		auto &staging = candidate->staging;
		const auto data = reuse_decode ? decoded_input(index, staging, group->banks, index.port(mux, ID::A))
					       : encoded_input(index, staging, *group, GetSize(output));
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

// 合并由状态控制的采样寄存器。
int merge_capture_banks(PmuxCoarseIndex &index, FfInitVals &initvals, const std::vector<IdString> &muxes)
{
	int changes = 0;
	for (auto name : muxes) {
		auto mux = index.module->cell(name);
		if (mux)
			changes += compress_bank_group(index, initvals, mux);
	}
	return changes;
}

// 用状态位连线替换可证明等价的 one-hot 比较器。
int simplify_onehot_decodes(PmuxCoarseIndex &index, FfInitVals &initvals, const std::vector<IdString> &decodes)
{
	int changes = 0;
	dict<Cell *, bool> onehot_states;
	for (auto name : decodes) {
		auto cell = index.module->cell(name);
		if (cell)
			changes += replace_decode(index, initvals, cell, onehot_states);
	}
	return changes;
}
// 在改写开始前记录候选单元的原始顺序。
int optimize_state_module(Module *module)
{
	PmuxCoarseIndex index(module);
	FfInitVals initvals(&index.sigmap, module);
	std::vector<IdString> muxes, decodes;
	for (auto cell : module->selected_cells()) {
		if (cell->type == ID($pmux))
			muxes.push_back(cell->name);
		else if (cell->type.in(ID($eq), ID($ne), ID($logic_not)))
			decodes.push_back(cell->name);
	}
	int changes = merge_capture_banks(index, initvals, muxes);
	return changes + simplify_onehot_decodes(index, initvals, decodes);
}

// 注册状态寄存器与译码化简 Pass。
struct OptPmuxStatePass : Pass {
	// 注册 opt_pmux_state 命令。
	OptPmuxStatePass() : Pass("opt_pmux_state", "simplify one-hot state and synchronous register groups") {}

	// 说明寄存器合并和 one-hot 译码的适用条件。
	void help() override
	{
		log("    opt_pmux_state [selection]\n\n");
		log("Replace comparisons of provably one-hot registers and combine synchronous\n");
		log("capture banks with complete state selection when fewer register bits suffice.\n");
	}

	// 对选中模块执行状态与寄存器优化。
	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		pmux_run_pass(design, "opt_pmux_state", "Executing OPT_PMUX_STATE pass.\n", optimize_state_module);
	}
} OptPmuxStatePass;

PRIVATE_NAMESPACE_END

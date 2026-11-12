#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

#include <array>
#include <numeric>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct SelectNetwork
{
	Cell *cell;
	SigSpec a, b, y;
	std::vector<int> branches;

	SigBit data(int branch, int offset) const
	{
		return branch < 0 ? a[offset] : b[branch * GetSize(y) + offset];
	}
};

class SelectWorker
{
	Module *module;
	PmuxCoarseIndex index;

	bool collect_removable(PmuxRewrite &rewrite, const pool<Cell *> &replaced, pool<Cell *> candidates,
			const SigSpec &output, const pool<SigBit> &inputs)
	{
		pool<SigBit> outputs;
		for (auto bit : index.sigmap(output))
			outputs.insert(bit);
		candidates.insert(replaced.begin(), replaced.end());
		rewrite.removed = index.removable(candidates, replaced, outputs, inputs);
		return std::all_of(replaced.begin(), replaced.end(), [&](auto cell) { return rewrite.removed.count(cell); });
	}

	std::unique_ptr<PmuxRewrite> rebuild(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding, bool specialize)
	{
		PmuxSelectTree tree(index, encoding);
		std::vector<int> controls(GetSize(encoding.controls)), roots;
		std::iota(controls.begin(), controls.end(), 0);
		SigSpec output;
		pool<Cell *> replaced;
		bool all_single = true, direct_column = false;
		for (const auto &network : networks) {
			all_single &= GetSize(network.cell->getPort(ID::S)) == 1;
			replaced.insert(network.cell);
			output.append(network.y);
			for (int offset = 0; offset < GetSize(network.y); ++offset) {
				std::vector<int> rows;
				for (int code = 0; code < GetSize(network.branches); ++code) {
					SigBit bit = network.data(network.branches[code], offset);
					auto slot = encoding.slots.find(bit);
					if (slot != encoding.slots.end())
						rows.push_back(tree.literal(code & (1 << slot->second) ? State::S1 : State::S0));
					else
						rows.push_back(specialize ? tree.fold(bit, code) : tree.literal(bit));
				}
				direct_column |= std::all_of(rows.begin(), rows.end(), [&](int row) { return row == rows.front(); });
				roots.push_back(tree.column(std::move(rows), controls));
			}
		}
		if (all_single && tree.mux_bits(roots) >= GetSize(output))
			return nullptr;
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, specialize ? "specialize_decoded_data" : "rebuild_decode");
		rewrite->connect(output, tree.emit(&rewrite->staging, roots, networks.front().cell->get_src_attribute()));
		pool<Cell *> candidates = encoding.cells;
		candidates.insert(tree.producers.begin(), tree.producers.end());
		if (!collect_removable(*rewrite, replaced, std::move(candidates), output, tree.inputs(roots)))
			return nullptr;
		if (!all_single && !direct_column && std::all_of(rewrite->removed.begin(), rewrite->removed.end(),
				[&](auto cell) { return replaced.count(cell); }))
			return nullptr;
		if (!rewrite->validate())
			return nullptr;
		return rewrite;
	}

	dict<Cell *, std::array<bool, 2>> foldable_mux_arms(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding)
	{
		std::vector<Cell *> cells;
		std::vector<uint64_t> active_codes;
		for (const auto &network : networks) {
			if (network.cell->type != ID($mux))
				continue;
			cells.push_back(network.cell);
			uint64_t codes = 0;
			for (int code = 0; code < GetSize(network.branches); ++code)
				if (network.branches[code] == 0)
					codes |= uint64_t(1) << code;
			active_codes.push_back(codes);
		}

		auto choices = encoding.partial_branches(cells);
		dict<Cell *, std::array<bool, 2>> foldable;
		for (auto cell : cells)
			foldable.emplace(cell, std::array{!choices.empty(), !choices.empty()});
		if (choices.empty())
			return foldable;

		const auto partial_codes = encoding.partial_codes();
		for (int row = 0; row < GetSize(partial_codes); ++row) {
			const auto &partial = partial_codes[row];
			unsigned fixed = partial.zero | partial.one;
			if (fixed == (1u << GetSize(encoding.controls)) - 1)
				continue;
			uint64_t completions = 0;
			for (unsigned code = partial.one; code < (1u << GetSize(encoding.controls)); ++code)
				if ((code & fixed) == partial.one)
					completions |= uint64_t(1) << code;
			for (int i = 0; i < GetSize(cells); ++i) {
				if (choices[i][row].second == -2)
					continue;
				// 未知选择会合并两路数据。只在该路有兼容的完整编码时采用特化值。
				auto &arms = foldable.at(cells[i]);
				arms[0] &= (completions & ~active_codes[i]) != 0;
				arms[1] &= (completions & active_codes[i]) != 0;
			}
		}
		return foldable;
	}

	std::unique_ptr<PmuxRewrite> keep_decode(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding)
	{
		struct FieldPlan {
			Cell *cell;
			SigSpec output, direct_output;
			int first, width;
		};
		PmuxSelectTree tree(index, encoding);
		std::vector<FieldPlan> plans;
		std::vector<int> roots;
		pool<Cell *> replaced;
		pool<SigBit> select_inputs;
		SigSpec outputs;
		std::optional<dict<Cell *, std::array<bool, 2>>> foldable;
		for (const auto &network : networks) {
			auto select = index.port(network.cell, ID::S);
			int branches = GetSize(select) + 1;
			std::vector<std::vector<int>> by_branch(branches);
			std::vector<int> direct;
			SigSpec y, direct_y;
			bool changed = false;
			for (int offset = 0; offset < GetSize(network.y); ++offset) {
				// -1 表示不可达，-2 表示同一分支的多个编码对应不同数据。
				std::vector<int> common(branches, -1);
				int constant_column = -1;
				for (int code = 0; code < GetSize(network.branches); ++code) {
					int branch = network.branches[code];
					int value = tree.fold(network.data(branch, offset), code);
					int &same = common[branch + 1];
					same = same == -1 || same == value ? value : -2;
					constant_column = constant_column == -1 || constant_column == value ? value : -2;
				}
				if (constant_column >= 0) {
					direct.push_back(constant_column);
					direct_y.append(network.y[offset]);
					changed = true;
					continue;
				}
				for (int row = 0; row < branches; ++row) {
					int original = tree.literal(network.data(row - 1, offset));
					int value = common[row] < 0 ? original : common[row];
					if (value != original && network.cell->type == ID($mux)) {
						if (!foldable)
							foldable = foldable_mux_arms(networks, encoding);
						if (!foldable->at(network.cell)[row])
							value = original;
					}
					by_branch[row].push_back(value);
					changed |= value != original;
				}
				y.append(network.y[offset]);
			}
			if (!changed)
				continue;
			plans.push_back({network.cell, y, direct_y, GetSize(roots), GetSize(y)});
			for (const auto &branch : by_branch)
				roots.insert(roots.end(), branch.begin(), branch.end());
			roots.insert(roots.end(), direct.begin(), direct.end());
			if (!y.empty())
				select_inputs.insert(select.begin(), select.end());
			replaced.insert(network.cell);
			outputs.append(network.y);
		}
		if (plans.empty())
			return nullptr;
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, "specialize_shared_decode");
		SigSpec data = tree.emit(&rewrite->staging, roots, networks.front().cell->get_src_attribute());
		for (const auto &plan : plans) {
			auto select = index.port(plan.cell, ID::S);
			int branch_data = plan.width * GetSize(select);
			if (plan.width) {
				auto a = data.extract(plan.first, plan.width);
				auto b = data.extract(plan.first + plan.width, branch_data);
				auto src = plan.cell->get_src_attribute();
				if (plan.cell->type == ID($mux))
					rewrite->staging.addMux(NEW_ID, a, b, select, plan.output, src);
				else
					rewrite->staging.addPmux(NEW_ID, a, b, select, plan.output, src);
			}
			if (!plan.direct_output.empty())
				rewrite->connect(plan.direct_output, data.extract(plan.first + plan.width + branch_data, GetSize(plan.direct_output)));
		}
		auto inputs = tree.inputs(roots);
		inputs.insert(select_inputs.begin(), select_inputs.end());
		pool<Cell *> candidates = encoding.cells;
		candidates.insert(tree.producers.begin(), tree.producers.end());
		if (!collect_removable(*rewrite, replaced, std::move(candidates), outputs, inputs) || !rewrite->validate())
			return nullptr;
		return rewrite;
	}

	bool rewrite(const std::vector<IdString> &names)
	{
		std::vector<SelectNetwork> networks;
		std::vector<SigSpec> selectors;
		int width = 0;
		for (auto name : names) {
			auto cell = module->cell(name);
			if (!cell || !index.editable(cell))
				continue;
			auto y = index.port(cell, ID::Y);
			width += GetSize(y);
			selectors.push_back(index.port(cell, ID::S));
			networks.push_back({cell, index.port(cell, ID::A), index.port(cell, ID::B), y, {}});
		}
		if (networks.empty())
			return false;
		PmuxEncoding encoding(index);
		std::vector<std::vector<int>> tables;
		if (!encoding.branch_tables(selectors, tables) || width > pmux_max_table_bits / GetSize(tables.front()))
			return false;
		for (int i = 0; i < GetSize(networks); ++i)
			networks[i].branches = std::move(tables[i]);
		pool<Cell *> selections;
		for (const auto &network : networks)
			selections.insert(network.cell);
		bool shared_decode = index.removable(encoding.cells, selections, {}, {}) != encoding.cells;
		auto commit = [](std::unique_ptr<PmuxRewrite> candidate) {
			if (!candidate)
				return false;
			candidate->commit();
			return true;
		};
		if (shared_decode && commit(keep_decode(networks, encoding)))
			return true;
		if (commit(rebuild(networks, encoding, true)) || commit(rebuild(networks, encoding, false)))
			return true;
		return !shared_decode && commit(keep_decode(networks, encoding));
	}

public:
	explicit SelectWorker(Module *module) : module(module), index(module) {}

	std::pair<int, int> run()
	{
		dict<SigSpec, std::vector<IdString>> groups;
		std::vector<Cell *> cells = module->selected_cells();
		std::sort(cells.begin(), cells.end(), [](auto a, auto b) { return a->name < b->name; });
		for (auto cell : cells) {
			if (!pmux_select_shape(cell) || !index.editable(cell))
				continue;
			PmuxEncoding encoding(index);
			std::vector<int> branches;
			if (encoding.branch_table(index.port(cell, ID::S), branches))
				groups[pmux_control_key(encoding)].push_back(cell->name);
		}
		int rewrites = 0, before = module->cells_size();
		auto apply = [&](const std::vector<IdString> &names) {
			bool changed = rewrite(names);
			rewrites += changed;
			return changed;
		};
		for (const auto &[control, names] : groups) {
			if (apply(names) || GetSize(names) == 1)
				continue;
			dict<SigSpec, std::vector<IdString>> selectors;
			for (auto name : names)
				if (auto cell = module->cell(name))
					selectors[index.port(cell, ID::S)].push_back(name);
			for (const auto &[select, subset] : selectors) {
				if (GetSize(subset) > 1 && GetSize(subset) < GetSize(names) && apply(subset))
					continue;
				for (auto name : subset)
					apply({name});
			}
		}
		return {rewrites, module->cells_size() - before};
	}
};

struct OptPmuxSelectPass : Pass
{
	OptPmuxSelectPass() : Pass("opt_pmux_select", "rebuild selection networks from decoded control signals") {}

	void help() override
	{
		log("    opt_pmux_select [selection]\n\n");
		log("Rebuild mutually exclusive mux selections and specialize their data by control encoding.\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing OPT_PMUX_SELECT pass (rebuild selection networks).\n");
		extra_args(args, 1, design);
		if (pmux_coarse_observes_undef(design))
			return;
		int rewrites = 0, cell_change = 0;
		for (auto module : design->selected_modules()) {
			if (module->has_processes())
				continue;
			auto [count, delta] = SelectWorker(module).run();
			rewrites += count;
			cell_change += delta;
		}
		log("Rebuilt %d selection networks (net RTLIL cell change: %+d).\n", rewrites, cell_change);
	}
} OptPmuxSelectPass;

PRIVATE_NAMESPACE_END

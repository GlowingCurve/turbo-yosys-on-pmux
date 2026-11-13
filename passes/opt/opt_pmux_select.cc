#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

#include <array>
#include <bit>
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

	bool merge_wrapper(Cell *outer)
	{
		if (outer->type != ID($mux) || !pmux_select_shape(outer) || !index.editable(outer))
			return false;
		SigSpec output = index.port(outer, ID::Y);
		for (IdString arm : {ID::A, ID::B}) {
			SigSpec inner_output = index.port(outer, arm);
			Cell *inner = index.driver(inner_output[0]);
			if (!inner || inner->type != ID($pmux) || !pmux_select_shape(inner) || !index.editable(inner) ||
					index.port(inner, ID::Y) != inner_output)
				continue;

			SigSpec bypass = index.port(outer, arm == ID::A ? ID::B : ID::A);
			pool<Cell *> replaced{inner, outer};
			pool<SigBit> outputs(output.begin(), output.end()), retained(bypass.begin(), bypass.end());
			if (index.removable(replaced, {}, outputs, retained) != replaced)
				continue;

			SigSpec inner_select = index.port(inner, ID::S);
			PmuxEncoding encoding(index);
			std::vector<std::vector<int>> tables;
			if (!encoding.branch_tables({inner_select, index.port(outer, ID::S)}, tables) ||
					GetSize(output) > pmux_max_table_bits / GetSize(tables.front()))
				continue;

			PmuxSelectTree tree(index, encoding);
			std::vector<int> controls(GetSize(encoding.controls)), roots;
			std::iota(controls.begin(), controls.end(), 0);
			SelectNetwork network{inner, index.port(inner, ID::A), index.port(inner, ID::B), inner_output, std::move(tables[0])};
			// 未知控制下，选择树会合并所有兼容编码的原始数据位。
			for (int offset = 0; offset < GetSize(output); ++offset) {
				std::vector<int> rows;
				for (int code = 0; code < GetSize(network.branches); ++code) {
					bool use_inner = (tables[1][code] == 0) == (arm == ID::B);
					rows.push_back(tree.literal(use_inner ? network.data(network.branches[code], offset) : bypass[offset]));
				}
				roots.push_back(tree.column(std::move(rows), controls));
			}
			if (tree.mux_bits(roots) >= GetSize(output) * (GetSize(inner_select) + 1))
				continue;

			PmuxRewrite rewrite(module, index, "merge_select_wrapper");
			rewrite.connect(output, tree.emit(&rewrite.staging, roots, outer->get_src_attribute()));
			if (!collect_removable(rewrite, replaced, encoding.cells, output, tree.inputs(roots)) ||
					GetSize(rewrite.removed) <= rewrite.added_count() || !rewrite.validate())
				continue;
			rewrite.commit();
			return true;
		}
		return false;
	}

	static unsigned data_support(const std::vector<SigBit> &rows)
	{
		unsigned mask = 0;
		for (unsigned bit = 1; bit < rows.size(); bit <<= 1)
			for (unsigned code = 0; code < rows.size(); ++code)
				if (!(code & bit) && rows[code] != rows[code | bit]) {
					mask |= bit;
					break;
				}
		return mask;
	}

	std::unique_ptr<PmuxRewrite> reduce_fields(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding)
	{
		if (encoding.controls.size() < 2 || std::none_of(networks.begin(), networks.end(), [](const auto &network) {
				return network.cell->type == ID($pmux);
			}))
			return nullptr;
		std::vector<PmuxPartialCode> partial_codes;
		unsigned full_mask = (1u << encoding.controls.size()) - 1;

		struct ReducedField {
			SigSpec output;
			std::vector<SigSpec> data;
		};
		std::map<unsigned, ReducedField> fields;
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, "reduce_selection_fields");
		pool<Cell *> replaced;
		pool<SigBit> inputs;
		SigSpec output;
		int saved_terms = 0;
		auto retain = [&](const SigSpec &signal) { inputs.insert(signal.begin(), signal.end()); };
		for (const auto &network : networks) {
			if (network.cell->type != ID($pmux))
				continue;
			SigSpec select = index.port(network.cell, ID::S);
			std::vector<unsigned> unknown_by_branch;
			auto parallel_safe = [&](unsigned mask, int offset) {
				if (unknown_by_branch.empty()) {
					auto branches = encoding.partial_branches({network.cell});
					unknown_by_branch.resize(GetSize(select) + 1, branches.empty() ? full_mask : 0);
					if (!branches.empty()) {
						if (partial_codes.empty())
							partial_codes = encoding.partial_codes();
						const auto &choices = branches.front();
						for (int row = 0; row < GetSize(choices); ++row) {
							int branch = choices[row].first;
							if (branch != -2)
								unknown_by_branch[branch + 1] |= full_mask & ~(partial_codes[row].zero | partial_codes[row].one);
						}
					}
				}
				// 并行译码在未知控制下可能输出 X，原分支的已定义数据必须保留。
				for (int branch = 0; branch < GetSize(unknown_by_branch); ++branch)
					if ((unknown_by_branch[branch] & mask) && network.data(branch - 1, offset) != State::Sx)
						return false;
				return true;
			};

			SigSpec remaining_output;
			std::vector<SigSpec> remaining(GetSize(select) + 1);
			std::vector<SigBit> rows(network.branches.size());
			for (int offset = 0; offset < GetSize(network.y); ++offset) {
				for (int code = 0; code < GetSize(rows); ++code)
					rows[code] = network.data(network.branches[code], offset);
				unsigned mask = data_support(rows);
				int controls = std::popcount(mask), reduced_branches = (1 << controls) - 1;
				bool reduces_terms = mask != full_mask && reduced_branches < GetSize(select) && (controls <= 1 || parallel_safe(mask, offset));
				if (!reduces_terms) {
					remaining_output.append(network.y[offset]);
					for (int branch = 0; branch < GetSize(remaining); ++branch)
						remaining[branch].append(network.data(branch - 1, offset));
					continue;
				}

				auto &field = fields[mask];
				field.output.append(network.y[offset]);
				field.data.resize(reduced_branches + 1);
				int reduced_code = 0;
				for (unsigned code = 0; code < rows.size(); ++code)
					if (!(code & ~mask))
						field.data[reduced_code++].append(rows[code]);
				saved_terms += GetSize(select) - reduced_branches;
			}
			if (remaining_output == network.y)
				continue;
			replaced.insert(network.cell);
			output.append(network.y);
			if (!remaining_output.empty()) {
				SigSpec data;
				for (int branch = 1; branch < GetSize(remaining); ++branch)
					data.append(remaining[branch]);
				retain(remaining.front());
				retain(data);
				retain(select);
				rewrite->staging.addPmux(NEW_ID, remaining.front(), data, select, remaining_output, network.cell->get_src_attribute());
			}
		}
		if (fields.empty())
			return nullptr;
		int decoder_bits = 0;
		for (const auto &[mask, field] : fields)
			if (std::popcount(mask) > 1)
				decoder_bits += std::popcount(mask) * (GetSize(field.data) - 1);
		if (saved_terms <= decoder_bits)
			return nullptr;

		const std::string src = networks.front().cell->get_src_attribute();
		for (const auto &[mask, field] : fields) {
			for (const auto &row : field.data)
				retain(row);
			SigSpec controls;
			for (int slot = 0; slot < GetSize(encoding.controls); ++slot)
				if (mask & (1u << slot))
					controls.append(encoding.controls[slot]);
			retain(controls);
			if (controls.empty()) {
				rewrite->connect(field.output, field.data.front());
			} else if (GetSize(controls) == 1) {
				rewrite->staging.addMux(NEW_ID, field.data[0], field.data[1], controls, field.output, src);
			} else {
				SigSpec selects(rewrite->staging.addWire(NEW_ID, GetSize(field.data) - 1));
				SigSpec data;
				for (int code = 1; code < GetSize(field.data); ++code) {
					rewrite->staging.addEq(NEW_ID, controls, Const(code, GetSize(controls)), selects[code - 1], false, src);
					data.append(field.data[code]);
				}
				rewrite->staging.addPmux(NEW_ID, field.data.front(), data, selects, field.output, src);
			}
		}
		if (!collect_removable(*rewrite, replaced, encoding.cells, output, inputs) || !rewrite->validate())
			return nullptr;
		return rewrite;
	}

	std::unique_ptr<PmuxRewrite> rebuild(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding, bool specialize)
	{
		PmuxSelectTree tree(index, encoding);
		std::vector<int> controls(GetSize(encoding.controls)), roots, reversed_roots;
		std::iota(controls.begin(), controls.end(), 0);
		std::vector<int> reversed_controls(controls.rbegin(), controls.rend()), reversed_codes;
		if (GetSize(controls) > 1) {
			for (int code = 0; code < (1 << GetSize(controls)); ++code) {
				int reversed_code = 0;
				for (int control : controls)
					reversed_code = (reversed_code << 1) | ((code >> control) & 1);
				reversed_codes.push_back(reversed_code);
			}
		}
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
				if (!reversed_codes.empty()) {
					std::vector<int> reversed_rows;
					reversed_rows.reserve(rows.size());
					for (int code : reversed_codes)
						reversed_rows.push_back(rows[code]);
					reversed_roots.push_back(tree.column(std::move(reversed_rows), reversed_controls));
				}
				roots.push_back(tree.column(std::move(rows), controls));
			}
		}
		pool<Cell *> candidates = encoding.cells;
		candidates.insert(tree.producers.begin(), tree.producers.end());
		auto build_candidate = [&](const std::vector<int> &values, int mux_count, const char *rule) -> std::unique_ptr<PmuxRewrite> {
			if (all_single && mux_count >= GetSize(output))
				return nullptr;
			auto rewrite = std::make_unique<PmuxRewrite>(module, index, rule);
			if (!collect_removable(*rewrite, replaced, candidates, output, tree.inputs(values)))
				return nullptr;
			if (!all_single && !direct_column && std::all_of(rewrite->removed.begin(), rewrite->removed.end(),
					[&](auto cell) { return replaced.count(cell); }))
				return nullptr;
			rewrite->connect(output, tree.emit(&rewrite->staging, values, networks.front().cell->get_src_attribute()));
			if (!rewrite->validate())
				return nullptr;
			return rewrite;
		};
		int mux_count = tree.mux_bits(roots);
		auto forward = build_candidate(roots, mux_count, specialize ? "specialize_decoded_data" : "rebuild_decode");
		if (reversed_roots.empty() || reversed_roots == roots)
			return forward;
		int reversed_mux_count = tree.mux_bits(reversed_roots);
		if (forward && reversed_mux_count > mux_count)
			return forward;
		auto reverse = build_candidate(reversed_roots, reversed_mux_count,
				specialize ? "specialize_decoded_data_reverse" : "rebuild_decode_reverse");
		auto rank = [](const PmuxRewrite &rewrite, int count) {
			return std::pair{count, rewrite.added_count() - GetSize(rewrite.removed)};
		};
		if (reverse && (!forward || rank(*reverse, reversed_mux_count) < rank(*forward, mux_count)))
			return reverse;
		return forward;
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

	std::unique_ptr<PmuxRewrite> specialize_data(const std::vector<SelectNetwork> &networks,
			const PmuxEncoding &encoding, bool shared_decode)
	{
		pool<Cell *> selections;
		for (const auto &network : networks)
			selections.insert(network.cell);
		bool shared = index.removable(encoding.cells, selections, {}, {}) != encoding.cells;
		return shared == shared_decode ? keep_decode(networks, encoding) : nullptr;
	}

	std::vector<Cell *> selected_cells(bool pmux_only) const
	{
		auto cells = module->selected_cells();
		if (pmux_only)
			std::erase_if(cells, [](auto cell) { return cell->type != ID($pmux); });
		std::sort(cells.begin(), cells.end(), [](auto a, auto b) { return a->name < b->name; });
		return cells;
	}

	template<typename Build>
	bool rewrite_group(std::vector<IdString> &names, bool pmux_only, bool retain_choices, Build build)
	{
		std::vector<SelectNetwork> networks;
		std::vector<SigSpec> selectors;
		int width = 0;
		for (auto name : names) {
			auto cell = module->cell(name);
			if (!cell || !pmux_select_shape(cell) || !index.editable(cell) || (pmux_only && cell->type != ID($pmux)))
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
		auto rewrite = build(networks, encoding);
		if (!rewrite)
			return false;
		if (retain_choices)
			for (auto cell : rewrite->staging.cells())
				if (cell->type == ID($pmux) || (!pmux_only && cell->type == ID($mux)))
					names.push_back(cell->name);
		rewrite->commit();
		std::erase_if(names, [&](IdString name) { return !module->cell(name); });
		std::sort(names.begin(), names.end());
		names.erase(std::unique(names.begin(), names.end()), names.end());
		return true;
	}

	int merge_wrappers()
	{
		std::vector<IdString> wrappers;
		for (auto cell : selected_cells(false))
			if (cell->type == ID($mux))
				wrappers.push_back(cell->name);
		int rewrites = 0;
		for (auto name : wrappers)
			if (auto cell = module->cell(name))
				rewrites += merge_wrapper(cell);
		return rewrites;
	}

	dict<SigSpec, std::vector<IdString>> group_networks(const std::vector<Cell *> &cells)
	{
		dict<SigSpec, std::vector<IdString>> groups;
		for (auto cell : cells) {
			if (!pmux_select_shape(cell) || !index.editable(cell))
				continue;
			PmuxEncoding encoding(index);
			std::vector<int> branches;
			if (encoding.branch_table(index.port(cell, ID::S), branches))
				groups[pmux_control_key(encoding)].push_back(cell->name);
		}
		return groups;
	}

	int rewrite_network(std::vector<IdString> names, bool pmux_only)
	{
		int rewrites = 0;
		rewrites += rewrite_group(names, pmux_only, true, [&](const auto &networks, const auto &encoding) {
			return reduce_fields(networks, encoding);
		});
		rewrites += rewrite_group(names, pmux_only, false, [&](const auto &networks, const auto &encoding) {
			return specialize_data(networks, encoding, true);
		});
		rewrites += rewrite_group(names, pmux_only, false, [&](const auto &networks, const auto &encoding) {
			return rebuild(networks, encoding, true);
		});
		rewrites += rewrite_group(names, pmux_only, false, [&](const auto &networks, const auto &encoding) {
			return rebuild(networks, encoding, false);
		});
		rewrites += rewrite_group(names, pmux_only, false, [&](const auto &networks, const auto &encoding) {
			return specialize_data(networks, encoding, false);
		});
		return rewrites;
	}

	int rewrite_networks(bool pmux_only)
	{
		int rewrites = 0;
		auto apply = [&](const std::vector<IdString> &names) {
			int changes = rewrite_network(names, pmux_only);
			rewrites += changes;
			return changes != 0;
		};
		auto groups = group_networks(selected_cells(pmux_only));
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
		return rewrites;
	}

public:
	explicit SelectWorker(Module *module) : module(module), index(module) {}

	std::pair<int, int> run(bool pmux_only)
	{
		int before = module->cells_size();
		int rewrites = pmux_only ? 0 : merge_wrappers();
		rewrites += rewrite_networks(pmux_only);
		return {rewrites, module->cells_size() - before};
	}
};

struct OptPmuxSelectPass : Pass
{
	OptPmuxSelectPass() : Pass("opt_pmux_select", "rebuild selection networks from decoded control signals") {}

	void help() override
	{
		log("    opt_pmux_select [-pmux-only] [selection]\n\n");
		log("Rebuild mutually exclusive mux selections and specialize their data by control encoding.\n");
		log("-pmux-only restricts rewrite roots to $pmux cells. Private decoder cells may still be removed.\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing OPT_PMUX_SELECT pass (rebuild selection networks).\n");
		bool pmux_only = args.size() > 1 && args[1] == "-pmux-only";
		extra_args(args, pmux_only ? 2 : 1, design);
		if (pmux_coarse_observes_undef(design))
			return;
		int rewrites = 0, cell_change = 0;
		for (auto module : design->selected_modules()) {
			if (module->has_processes())
				continue;
			auto [count, delta] = SelectWorker(module).run(pmux_only);
			rewrites += count;
			cell_change += delta;
		}
		log("Rebuilt %d selection networks (net RTLIL cell change: %+d).\n", rewrites, cell_change);
	}
} OptPmuxSelectPass;

PRIVATE_NAMESPACE_END

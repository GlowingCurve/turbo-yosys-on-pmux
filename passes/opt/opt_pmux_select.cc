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
	SigSpec a, b, select, y;
	std::vector<int> branches;

	SelectNetwork(PmuxCoarseIndex &index, Cell *cell) : cell(cell),
		a(index.port(cell, ID::A)), b(index.port(cell, ID::B)), select(index.port(cell, ID::S)),
		y(index.port(cell, ID::Y)) {}

	int arms() const { return GetSize(select) + 1; }

	SigBit data(int branch, int offset) const
	{
		return branch == 0 ? a[offset] : b[(branch - 1) * GetSize(y) + offset];
	}

	SigBit encoded_data(int code, int offset) const { return data(branches[code], offset); }
};

class SelectWorker
{
	Module *module;
	PmuxCoarseIndex index;

	struct SelectorAnalysis {
		PmuxEncoding encoding;
		std::vector<int> branches;

		SelectorAnalysis(PmuxCoarseIndex &index, const SigSpec &select) :
			encoding(index)
		{
			encoding.branch_table(select, branches);
		}
	};
	dict<SigSpec, std::unique_ptr<SelectorAnalysis>> selectors;

	const SelectorAnalysis &decode_selector(const SigSpec &select)
	{
		auto &analysis = selectors[select];
		if (!analysis)
			analysis = std::make_unique<SelectorAnalysis>(index, select);
		return *analysis;
	}

	bool collect_removable(PmuxRewrite &rewrite, const pool<Cell *> &replaced, pool<Cell *> candidates)
	{
		candidates.insert(replaced.begin(), replaced.end());
		rewrite.find_removable(candidates, replaced);
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
			std::vector<int> controls(GetSize(encoding.controls())), roots, rows(tables[1].size());
			std::iota(controls.begin(), controls.end(), 0);
			SelectNetwork network(index, inner);
			network.branches = std::move(tables[0]);
			// 未知控制下，选择树会合并所有兼容编码的原始数据位。
			for (int offset = 0; offset < GetSize(output); ++offset) {
				for (int code = 0; code < GetSize(rows); ++code) {
					bool use_inner = (tables[1][code] == 1) == (arm == ID::B);
					rows[code] = tree.literal(use_inner ? network.encoded_data(code, offset) : bypass[offset]);
				}
				roots.push_back(tree.column(rows, controls));
			}
			auto live = tree.analyze(roots);
			if (live.mux_bits >= GetSize(output) * (GetSize(inner_select) + 1))
				continue;
			PmuxRewrite rewrite(module, index, "merge_select_wrapper");
			rewrite.connect(output, tree.emit(&rewrite.staging, roots, outer->get_src_attribute(), live));
			if (!collect_removable(rewrite, replaced, encoding.cells()) ||
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
		if (encoding.controls().size() < 2 || std::none_of(networks.begin(), networks.end(),
				[](const auto &network) { return network.cell->type == ID($pmux); }))
			return nullptr;
		std::vector<PmuxPartialCode> partial_codes;
		unsigned full_mask = (1u << encoding.controls().size()) - 1;

		struct ReducedField {
			SigSpec output;
			std::vector<SigSpec> data;
		};
		std::map<unsigned, ReducedField> fields;
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, "reduce_selection_fields");
		pool<Cell *> replaced;
		int saved_terms = 0;
		for (const auto &network : networks) {
			if (network.cell->type != ID($pmux))
				continue;
			const auto &select = network.select;
			std::vector<unsigned> unknown_by_branch;
			auto parallel_safe = [&](unsigned mask, int offset) {
				if (unknown_by_branch.empty()) {
					auto choices = encoding.partial_branches({network.cell}).front();
					if (partial_codes.empty())
						partial_codes = encoding.partial_codes();
					unknown_by_branch.resize(network.arms());
					for (int row = 0; row < GetSize(choices); ++row)
						if (choices[row].kind == BranchKind::Selected)
							unknown_by_branch[choices[row].index] |= full_mask & ~(partial_codes[row].zero | partial_codes[row].one);
				}
				// 并行译码在未知控制下可能输出 X，原分支的已定义数据必须保留。
				for (int branch = 0; branch < GetSize(unknown_by_branch); ++branch)
					if ((unknown_by_branch[branch] & mask) && network.data(branch, offset) != State::Sx)
						return false;
				return true;
			};

			SigSpec remaining_output;
			std::vector<SigSpec> remaining(network.arms());
			std::vector<SigBit> rows(network.branches.size());
			for (int offset = 0; offset < GetSize(network.y); ++offset) {
				for (int code = 0; code < GetSize(rows); ++code)
					rows[code] = network.encoded_data(code, offset);
				unsigned mask = data_support(rows);
				int controls = std::popcount(mask), terms = pmux_encoding_limit(controls) - 1;
				if (mask == full_mask || terms >= GetSize(select) || (controls > 1 && !parallel_safe(mask, offset))) {
					remaining_output.append(network.y[offset]);
					for (int branch = 0; branch < GetSize(remaining); ++branch)
						remaining[branch].append(network.data(branch, offset));
					continue;
				}

				auto &field = fields[mask];
				field.output.append(network.y[offset]);
				field.data.resize(terms + 1);
				int reduced_code = 0;
				for (unsigned code = 0; code < rows.size(); ++code)
					if (!(code & ~mask))
						field.data[reduced_code++].append(rows[code]);
				saved_terms += GetSize(select) - terms;
			}
			if (remaining_output == network.y)
				continue;
			replaced.insert(network.cell);
			if (!remaining_output.empty()) {
				SigSpec data;
				for (int branch = 1; branch < GetSize(remaining); ++branch)
					data.append(remaining[branch]);
				rewrite->staging.addPmux(NEW_ID, remaining.front(), data, select, remaining_output, network.cell->get_src_attribute());
			}
		}
		for (const auto &[mask, field] : fields)
			if (std::popcount(mask) > 1)
				saved_terms -= std::popcount(mask) * (GetSize(field.data) - 1);
		if (saved_terms <= 0)
			return nullptr;

		const std::string src = networks.front().cell->get_src_attribute();
		for (const auto &[mask, field] : fields) {
			SigSpec controls;
			for (int slot = 0; slot < GetSize(encoding.controls()); ++slot)
				if (mask & (1u << slot))
					controls.append(encoding.controls()[slot]);
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
		if (!collect_removable(*rewrite, replaced, encoding.cells()) || !rewrite->validate())
			return nullptr;
		return rewrite;
	}

	std::unique_ptr<PmuxRewrite> rebuild(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding, bool specialize)
	{
		PmuxSelectTree tree(index, encoding);
		int control_count = GetSize(encoding.controls());
		std::vector<int> controls(control_count);
		std::iota(controls.begin(), controls.end(), 0);
		auto reversed_controls = controls;
		std::reverse(reversed_controls.begin(), reversed_controls.end());
		bool try_reverse = control_count > 1;
		std::vector<int> reversed_codes(try_reverse ? pmux_encoding_limit(control_count) : 0);
		for (int code = 0; code < GetSize(reversed_codes); ++code)
			for (int control : controls)
				reversed_codes[code] = (reversed_codes[code] << 1) | ((code >> control) & 1);

		std::array<std::vector<int>, 2> roots;
		auto append_column = [&](std::vector<int> values, bool reverse) {
			if (reverse)
				for (int row = 0; row < GetSize(values); ++row)
					if (row < reversed_codes[row])
						std::swap(values[row], values[reversed_codes[row]]);
			roots[reverse].push_back(tree.column(std::move(values), reverse ? reversed_controls : controls));
		};
		SigSpec output;
		pool<Cell *> replaced;
		bool all_single = true, direct_column = false;
		for (const auto &network : networks) {
			all_single &= GetSize(network.select) == 1;
			replaced.insert(network.cell);
			output.append(network.y);
			for (int offset = 0; offset < GetSize(network.y); ++offset) {
				std::vector<int> rows(network.branches.size());
				for (int code = 0; code < GetSize(rows); ++code) {
					SigBit bit = network.encoded_data(code, offset);
					if (auto slot = encoding.slots().find(bit); slot != encoding.slots().end())
						rows[code] = tree.literal(code & (1 << slot->second) ? State::S1 : State::S0);
					else
						rows[code] = specialize ? tree.fold(bit, code) : tree.literal(bit);
				}
				direct_column |= std::all_of(rows.begin(), rows.end(), [&](int row) { return row == rows.front(); });
				if (try_reverse)
					append_column(rows, true);
				append_column(std::move(rows), false);
			}
		}
		pool<Cell *> candidates = encoding.cells();
		candidates.insert(tree.producers.begin(), tree.producers.end());
		const char *rules[2][2] = {
			{"rebuild_decode", "rebuild_decode_reverse"},
			{"specialize_decoded_data", "specialize_decoded_data_reverse"},
		};
		auto build_candidate = [&](bool reverse, const PmuxSelectTree::Analysis &live) -> std::unique_ptr<PmuxRewrite> {
			if (all_single && live.mux_bits >= GetSize(output))
				return nullptr;
			auto rewrite = std::make_unique<PmuxRewrite>(module, index, rules[specialize][reverse]);
			rewrite->connect(output, tree.emit(&rewrite->staging, roots[reverse], networks.front().cell->get_src_attribute(), live));
			if (!collect_removable(*rewrite, replaced, candidates) ||
					(!all_single && !direct_column && rewrite->removed.size() == replaced.size()) || !rewrite->validate())
				return nullptr;
			return rewrite;
		};
		auto live = tree.analyze(roots[false]);
		auto forward = build_candidate(false, live);
		if (!try_reverse || roots[true] == roots[false])
			return forward;
		auto reversed_live = tree.analyze(roots[true]);
		if (forward && reversed_live.mux_bits > live.mux_bits)
			return forward;
		auto reverse = build_candidate(true, reversed_live);
		auto rank = [](const PmuxRewrite &rewrite, int count) {
			return std::pair{count, rewrite.added_count() - GetSize(rewrite.removed)};
		};
		if (reverse && (!forward || rank(*reverse, reversed_live.mux_bits) < rank(*forward, live.mux_bits)))
			return reverse;
		return forward;
	}

	std::unique_ptr<PmuxRewrite> preserve_shared_control(const std::vector<SelectNetwork> &networks,
			const PmuxEncoding &encoding, PmuxRewrite &original)
	{
		if (encoding.controls().size() == pmux_max_controls)
			return nullptr;
		std::optional<SigBit> data_control;
		int width = 0;
		auto input = [&](SigBit bit) { return !bit.wire || index.module_input(bit); };
		for (const auto &network : networks) {
			width += GetSize(network.y);
			for (const auto &data : {network.a, network.b})
				for (auto bit : data) {
					if (input(bit))
						continue;
					auto source = index.source(bit);
					if (!source || source->port != ID::Y || source->cell->type != ID($mux) || !pmux_select_shape(source->cell))
						return nullptr;
					auto cell = source->cell;
					if (!input(index.port(cell, ID::A)[source->offset]) || !input(index.port(cell, ID::B)[source->offset]))
						return nullptr;
					auto select = index.port(cell, ID::S)[0];
					if (data_control && *data_control != select)
						return nullptr;
					data_control = select;
				}
		}
		if (!data_control)
			return nullptr;
		auto control_source = index.source(*data_control);
		if (!control_source || !control_source->cell->type.in(ID($xor), ID($xnor)))
			return nullptr;
		PmuxEncoding expanded(encoding);
		// 将已共享的奇偶控制作为独立变量保留。
		if (!expanded.pin(*data_control) || expanded.controls().size() == encoding.controls().size() ||
				width > pmux_max_table_bits / pmux_encoding_limit(GetSize(expanded.controls())))
			return nullptr;
		std::vector<SigSpec> selects;
		for (const auto &network : networks)
			selects.push_back(network.select);
		std::vector<std::vector<int>> tables;
		if (!expanded.branch_tables(selects, tables))
			return nullptr;
		auto expanded_networks = networks;
		for (int pos = 0; pos < GetSize(networks); ++pos)
			expanded_networks[pos].branches = std::move(tables[pos]);
		auto rewrite = rebuild(expanded_networks, expanded, true);
		if (!rewrite || logic_cost(*rewrite) >= logic_cost(original))
			return nullptr;
		log_debug("PMUX shared_parity_control in %s: selected (gate cost %d -> %d).\n",
			log_id(module), logic_cost(original), logic_cost(*rewrite));
		return rewrite;
	}

	static int logic_cost(PmuxRewrite &rewrite)
	{
		auto cell_cost = [](Cell *cell) {
			int width = GetSize(cell->getPort(ID::Y));
			if (cell->type == ID($pmux))
				return width * (2 * GetSize(cell->getPort(ID::S)) - 1);
			return width * (cell->type.in(ID($mux), ID($xor), ID($xnor)) ? 3 : 1);
		};
		int cost = 0;
		for (auto cell : rewrite.staging.cells())
			cost += cell_cost(cell);
		for (auto cell : rewrite.removed)
			cost -= cell_cost(cell);
		return cost;
	}

	dict<Cell *, std::array<bool, 2>> foldable_mux_arms(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding)
	{
		std::vector<const SelectNetwork *> muxes;
		std::vector<Cell *> cells;
		for (const auto &network : networks) {
			if (network.cell->type == ID($mux)) {
				muxes.push_back(&network);
				cells.push_back(network.cell);
			}
		}

		auto choices = encoding.partial_branches(cells);
		const auto partial_codes = encoding.partial_codes();
		unsigned row_count = pmux_encoding_limit(GetSize(encoding.controls()));
		std::vector<uint64_t> completions(partial_codes.size());
		for (int row = 0; row < GetSize(partial_codes); ++row) {
			const auto &[zero, one] = partial_codes[row];
			unsigned fixed = zero | one;
			for (unsigned code = one; code < row_count; ++code)
				if ((code & fixed) == one)
					completions[row] |= uint64_t(1) << code;
		}
		dict<Cell *, std::array<bool, 2>> foldable;
		for (int i = 0; i < GetSize(cells); ++i) {
			uint64_t active = 0;
			for (unsigned code = 0; code < row_count; ++code)
				if (muxes[i]->branches[code] == 1)
					active |= uint64_t(1) << code;
			std::array arms{true, true};
			// An unknown selector merges both arms. Each arm needs a compatible complete code.
			for (int row = 0; row < GetSize(completions); ++row)
				if (choices[i][row].kind == BranchKind::Dynamic) {
					arms[0] &= (completions[row] & ~active) != 0;
					arms[1] &= (completions[row] & active) != 0;
				}
			foldable.emplace(cells[i], arms);
		}
		return foldable;
	}

	std::unique_ptr<PmuxRewrite> keep_decode(const std::vector<SelectNetwork> &networks, const PmuxEncoding &encoding, bool shared)
	{
		struct FieldPlan {
			Cell *cell;
			SigSpec output, direct_output;
			int first;
		};
		struct BranchChoice {
			enum class Kind { unreachable, fixed, dynamic } kind = Kind::unreachable;
			int value = 0;

			void include(int next)
			{
				if (kind == Kind::unreachable)
					*this = {Kind::fixed, next};
				else if (value != next)
					kind = Kind::dynamic;
			}
		};
		PmuxSelectTree tree(index, encoding);
		std::vector<FieldPlan> plans;
		std::vector<int> roots;
		pool<Cell *> replaced;
		std::optional<dict<Cell *, std::array<bool, 2>>> foldable;
		for (const auto &network : networks) {
			std::vector<std::vector<int>> by_branch(network.arms());
			std::vector<int> direct;
			SigSpec y, direct_y;
			bool changed = false;
			std::vector<BranchChoice> common(network.arms());
			for (int offset = 0; offset < GetSize(network.y); ++offset) {
				std::fill(common.begin(), common.end(), BranchChoice{});
				BranchChoice column;
				for (int code = 0; code < GetSize(network.branches); ++code) {
					int branch = network.branches[code];
					int value = tree.fold(network.data(branch, offset), code);
					common[branch].include(value);
					column.include(value);
				}
				if (column.kind == BranchChoice::Kind::fixed) {
					direct.push_back(column.value);
					direct_y.append(network.y[offset]);
					changed = true;
					continue;
				}
				for (int row = 0; row < GetSize(common); ++row) {
					int original = tree.literal(network.data(row, offset));
					int value = common[row].kind == BranchChoice::Kind::fixed ? common[row].value : original;
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
			plans.push_back({network.cell, y, direct_y, GetSize(roots)});
			for (const auto &branch : by_branch)
				roots.insert(roots.end(), branch.begin(), branch.end());
			roots.insert(roots.end(), direct.begin(), direct.end());
			replaced.insert(network.cell);
		}
		if (replaced.empty())
			return nullptr;
		auto live = tree.analyze(roots);
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, shared ? "specialize_shared_decode" : "specialize_dedicated_decode");
		SigSpec data = tree.emit(&rewrite->staging, roots, networks.front().cell->get_src_attribute(), live);
		for (const auto &plan : plans) {
			auto select = index.port(plan.cell, ID::S);
			int width = GetSize(plan.output), branch_data = width * GetSize(select);
			if (width) {
				auto a = data.extract(plan.first, width);
				auto b = data.extract(plan.first + width, branch_data);
				auto src = plan.cell->get_src_attribute();
				if (plan.cell->type == ID($mux))
					rewrite->staging.addMux(NEW_ID, a, b, select, plan.output, src);
				else
					rewrite->staging.addPmux(NEW_ID, a, b, select, plan.output, src);
			}
			if (!plan.direct_output.empty())
				rewrite->connect(plan.direct_output, data.extract(plan.first + width + branch_data, GetSize(plan.direct_output)));
		}
		pool<Cell *> candidates = encoding.cells();
		candidates.insert(tree.producers.begin(), tree.producers.end());
		if (!collect_removable(*rewrite, replaced, std::move(candidates)) ||
				(!shared && GetSize(rewrite->removed) <= rewrite->added_count()) || !rewrite->validate())
			return nullptr;
		return rewrite;
	}

	std::vector<IdString> selected_names() const
	{
		std::vector<IdString> names;
		for (auto cell : module->selected_cells())
			if (pmux_select_shape(cell))
				names.push_back(cell->name);
		std::sort(names.begin(), names.end());
		return names;
	}

	template<typename Key>
	std::vector<std::vector<IdString>> group_networks(const std::vector<IdString> &names, Key &&key)
	{
		dict<SigSpec, int> positions;
		std::vector<std::vector<IdString>> groups;
		for (auto name : names)
			if (auto cell = module->cell(name))
				if (auto value = key(cell)) {
					auto [position, inserted] = positions.emplace(std::move(*value), GetSize(groups));
					if (inserted)
						groups.emplace_back();
					groups[position->second].push_back(name);
				}
		std::reverse(groups.begin(), groups.end());
		return groups;
	}

	int rewrite_network(std::vector<IdString> names, bool pmux_only)
	{
		enum class Rule { reduce, shared, specialize, rebuild_raw, dedicated };
		const std::array rules{Rule::reduce, Rule::shared, Rule::dedicated, Rule::specialize, Rule::rebuild_raw};
		int next_rule = 0;
		int rewrites = 0;
		while (next_rule < GetSize(rules)) {
			std::vector<SelectNetwork> networks;
			std::vector<SigSpec> select_signals;
			pool<Cell *> selection_cells;
			int width = 0;
			for (auto name : names) {
				auto cell = module->cell(name);
				if (!cell || !pmux_select_shape(cell) || !index.editable(cell) || (pmux_only && cell->type != ID($pmux)))
					continue;
				const auto &network = networks.emplace_back(index, cell);
				select_signals.push_back(network.select);
				selection_cells.insert(cell);
				width += GetSize(network.y);
			}
			if (networks.empty())
				break;
			const auto &initial = decode_selector(select_signals.front());
			if (initial.branches.empty())
				break;
			const PmuxEncoding *encoding = &initial.encoding;
			std::optional<PmuxEncoding> combined;
			if (std::all_of(select_signals.begin(), select_signals.end(), [&](const auto &select) { return select == select_signals.front(); })) {
				for (auto &network : networks)
					network.branches = initial.branches;
			} else {
				combined.emplace(initial.encoding);
				encoding = &*combined;
				std::vector<std::vector<int>> tables;
				if (!combined->branch_tables(select_signals, tables))
					break;
				for (int i = 0; i < GetSize(networks); ++i)
					networks[i].branches = std::move(tables[i]);
			}
			if (width > pmux_max_table_bits / GetSize(networks.front().branches))
				break;

			std::optional<bool> shared_decode;
			while (next_rule < GetSize(rules)) {
				std::unique_ptr<PmuxRewrite> rewrite;
				auto rule = rules[next_rule++];
				if (rule == Rule::reduce) {
					rewrite = reduce_fields(networks, *encoding);
				} else if (rule == Rule::shared || rule == Rule::dedicated) {
					if (!shared_decode)
						shared_decode = index.removable(encoding->cells(), selection_cells, {}, {}) != encoding->cells();
					if (*shared_decode == (rule == Rule::shared))
						rewrite = keep_decode(networks, *encoding, *shared_decode);
				} else {
					rewrite = rebuild(networks, *encoding, rule == Rule::specialize);
					if (rule == Rule::specialize && rewrite)
						if (auto shared = preserve_shared_control(networks, *encoding, *rewrite))
							rewrite = std::move(shared);
				}
				if (!rewrite)
					continue;
				if (rule == Rule::reduce) {
					for (auto cell : rewrite->staging.cells())
						if (cell->type == ID($pmux) || (!pmux_only && cell->type == ID($mux)))
							names.push_back(cell->name);
					std::sort(names.begin(), names.end());
					names.erase(std::unique(names.begin(), names.end()), names.end());
				}
				rewrite->commit();
				selectors.clear();
				++rewrites;
				break;
			}
		}
		return rewrites;
	}

public:
	explicit SelectWorker(Module *module) : module(module), index(module) {}

	int run(bool pmux_only)
	{
		int rewrites = 0;
		if (!pmux_only)
			for (auto name : selected_names())
				if (auto cell = module->cell(name))
					rewrites += merge_wrapper(cell);
		auto groups = group_networks(selected_names(), [&](Cell *cell) -> std::optional<SigSpec> {
			if ((pmux_only && cell->type != ID($pmux)) || !index.editable(cell))
				return std::nullopt;
			const auto &analysis = decode_selector(index.port(cell, ID::S));
			if (analysis.branches.empty())
				return std::nullopt;
			return analysis.encoding.control_key();
		});
		auto apply = [&](const std::vector<IdString> &names) {
			int changes = rewrite_network(names, pmux_only);
			rewrites += changes;
			return changes != 0;
		};
		for (const auto &names : groups) {
			if (apply(names) || GetSize(names) == 1)
				continue;
			for (const auto &subset : group_networks(names, [&](Cell *cell) {
				return std::optional(index.port(cell, ID::S));
			})) {
				if (GetSize(subset) > 1 && GetSize(subset) < GetSize(names) && apply(subset))
					continue;
				for (auto name : subset)
					apply({name});
			}
		}
		return rewrites;
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
		bool pmux_only = args.size() > 1 && args[1] == "-pmux-only";
		extra_args(args, pmux_only ? 2 : 1, design);
		pmux_run_pass(design, "opt_pmux_select", "Executing OPT_PMUX_SELECT pass (rebuild selection networks).\n",
			[&](Module *module) { return SelectWorker(module).run(pmux_only); });
	}
} OptPmuxSelectPass;

PRIVATE_NAMESPACE_END

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

// 优化方法层的选择树重建。合并嵌套选择器，按控制编码共享译码并精简数据选择。

#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

#include <array>
#include <bit>
#include <numeric>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 保存一组选择信号的控制编码和分支表。
struct SelectorAnalysis {
	PmuxEncoding encoding;
	std::vector<int> branches;

	// 为新遇到的选择条件建立分支映射。
	SelectorAnalysis(PmuxCoarseIndex &index, const SigSpec &select) : encoding(index) { encoding.branch_table(select, branches); }
};
using SelectorCache = dict<SigSpec, std::unique_ptr<SelectorAnalysis>>;

// 复用按完整选择信号缓存的译码结果。
const SelectorAnalysis &decode_selector(PmuxCoarseIndex &index, SelectorCache &selectors, const SigSpec &select)
{
	auto &analysis = selectors[select];
	if (!analysis)
		analysis = std::make_unique<SelectorAnalysis>(index, select);
	return *analysis;
}

// 按嵌套选择器的完整编码，为每个输出位建立选择树。
std::vector<int> wrapper_columns(PmuxSelectTree &tree, const PmuxEncoding &encoding, const PmuxEncodedChoice &network,
				 const std::vector<int> &outer_rows, const SigSpec &bypass, IdString arm)
{
	std::vector<int> controls(GetSize(encoding.controls()));
	std::iota(controls.begin(), controls.end(), 0);
	std::vector<int> roots;
	std::vector<int> rows(outer_rows.size());
	// 未知控制下，选择树会合并所有兼容编码的原始数据位。
	for (int offset = 0; offset < network.width(); ++offset) {
		for (int code = 0; code < GetSize(rows); ++code) {
			bool use_inner = (outer_rows[code] == 1) == (arm == ID::B);
			rows[code] = tree.literal(use_inner ? network.encoded_data(code, offset) : bypass[offset]);
		}
		roots.push_back(tree.column(rows, controls));
	}
	return roots;
}

// 合并外层二选一单元和内层并行选择器。
bool merge_wrapper(PmuxCoarseIndex &index, Cell *outer)
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
		pool<SigBit> outputs(output.begin(), output.end());
		pool<SigBit> retained(bypass.begin(), bypass.end());
		if (index.removable(replaced, {}, outputs, retained) != replaced)
			continue;

		SigSpec inner_select = index.port(inner, ID::S);
		PmuxEncoding encoding(index);
		std::vector<std::vector<int>> tables;
		if (!encoding.branch_tables({inner_select, index.port(outer, ID::S)}, tables) ||
		    GetSize(output) > pmux_max_table_bits / GetSize(tables.front()))
			continue;

		PmuxSelectTree tree(index, encoding);
		PmuxEncodedChoice network(index, inner);
		network.rows = std::move(tables[0]);
		auto roots = wrapper_columns(tree, encoding, network, tables[1], bypass, arm);
		auto live = tree.analyze(roots);
		if (live.mux_bits >= GetSize(output) * (GetSize(inner_select) + 1))
			continue;
		PmuxRewrite rewrite(index.module, index, "merge_select_wrapper");
		rewrite.connect(output, tree.emit(&rewrite.staging, roots, outer->get_src_attribute(), live));
		if (!rewrite.prepare(encoding.cells(), replaced, replaced) || GetSize(rewrite.removed) <= rewrite.added_count())
			continue;
		rewrite.commit();
		return true;
	}
	return false;
}

// 逐位翻转控制编码，找出会改变输出的控制位。
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

// 聚合同一组控制位可以驱动的输出。
struct ReducedField {
	SigSpec output;
	std::vector<SigSpec> data;
};

// 检查部分控制位未知时，原电路仍能给出确定数据的分支。
bool parallel_field_safe(const PmuxEncodedChoice &network, const PmuxEncoding &encoding, std::optional<PmuxPartialTable> &partial,
			 std::vector<unsigned> &unknown_by_branch, unsigned mask, int offset)
{
	if (unknown_by_branch.empty()) {
		auto choices = encoding.partial_branches({network.cell}).front();
		if (!partial)
			partial.emplace(encoding);
		unknown_by_branch.resize(network.branches());
		for (int row = 0; row < GetSize(choices); ++row)
			if (choices[row].kind == BranchKind::Selected)
				unknown_by_branch[choices[row].index] |= partial->unknown(row);
	}
	// 并行译码在未知控制下可能输出 X，原分支的已定义数据必须保留。
	for (int branch = 0; branch < GetSize(unknown_by_branch); ++branch)
		if ((unknown_by_branch[branch] & mask) && network.bit(branch, offset) != State::Sx)
			return false;
	return true;
}

// 识别各输出位依赖的控制位子集，保留仍需完整译码的输出切片。
int collect_reduced_fields(PmuxRewrite &rewrite, const PmuxEncodedChoice &network, const PmuxEncoding &encoding,
			   std::optional<PmuxPartialTable> &partial, std::map<unsigned, ReducedField> &fields, pool<Cell *> &replaced)
{
	int saved_terms = 0;
	unsigned full_mask = (1u << encoding.controls().size()) - 1;
	const auto &select = network.select;
	std::vector<unsigned> unknown_by_branch;
	std::vector<int> remaining;
	std::vector<SigBit> rows(network.rows.size());
	for (int offset = 0; offset < GetSize(network.y); ++offset) {
		for (int code = 0; code < GetSize(rows); ++code)
			rows[code] = network.encoded_data(code, offset);
		unsigned mask = data_support(rows);
		int controls = std::popcount(mask);
		int terms = pmux_encoding_limit(controls) - 1;
		if (mask == full_mask || terms >= GetSize(select) ||
		    (controls > 1 && !parallel_field_safe(network, encoding, partial, unknown_by_branch, mask, offset))) {
			remaining.push_back(offset);
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
	if (GetSize(remaining) != network.width()) {
		replaced.insert(network.cell);
		network.emit_slice(rewrite.staging, remaining);
	}
	return saved_terms;
}

// 对精简后的控制位生成连线、二选一单元或并行选择器。
void emit_reduced_fields(PmuxRewrite &rewrite, const std::map<unsigned, ReducedField> &fields, const PmuxEncoding &encoding, const std::string &src)
{
	for (const auto &[mask, field] : fields) {
		SigSpec controls;
		for (int slot = 0; slot < GetSize(encoding.controls()); ++slot)
			if (mask & (1u << slot))
				controls.append(encoding.controls()[slot]);
		if (controls.empty()) {
			rewrite.connect(field.output, field.data.front());
		} else if (GetSize(controls) == 1) {
			rewrite.staging.addMux(NEW_ID, field.data[0], field.data[1], controls, field.output, src);
		} else {
			SigSpec selects(rewrite.staging.addWire(NEW_ID, GetSize(field.data) - 1));
			SigSpec data;
			for (int code = 1; code < GetSize(field.data); ++code) {
				rewrite.staging.addEq(NEW_ID, controls, Const(code, GetSize(controls)), selects[code - 1], false, src);
				data.append(field.data[code]);
			}
			rewrite.staging.addPmux(NEW_ID, field.data.front(), data, selects, field.output, src);
		}
	}
}

// 对同组选择器精简字段并检查总收益。
std::unique_ptr<PmuxRewrite> reduce_selection_fields(PmuxCoarseIndex &index, const std::vector<PmuxEncodedChoice> &networks,
						     const PmuxEncoding &encoding)
{
	if (encoding.controls().size() < 2 ||
	    std::none_of(networks.begin(), networks.end(), [](const auto &network) { return network.cell->type == ID($pmux); }))
		return nullptr;
	std::optional<PmuxPartialTable> partial;
	std::map<unsigned, ReducedField> fields;
	auto rewrite = std::make_unique<PmuxRewrite>(index.module, index, "reduce_selection_fields");
	pool<Cell *> replaced;
	int saved_terms = 0;
	for (const auto &network : networks)
		if (network.cell->type == ID($pmux))
			saved_terms += collect_reduced_fields(*rewrite, network, encoding, partial, fields, replaced);
	for (const auto &[mask, field] : fields)
		if (std::popcount(mask) > 1)
			saved_terms -= std::popcount(mask) * (GetSize(field.data) - 1);
	if (saved_terms <= 0)
		return nullptr;
	emit_reduced_fields(*rewrite, fields, encoding, networks.front().cell->get_src_attribute());
	if (!rewrite->prepare(encoding.cells(), replaced, replaced))
		return nullptr;
	return rewrite;
}

// 保存两个控制顺序生成的选择树根节点及其输出位置。
struct TreeColumns {
	std::array<std::vector<int>, 2> roots;
	SigSpec output;
	pool<Cell *> replaced;
	bool all_single = true;
	bool direct_column = false;
};

// 按正向和反向控制顺序为各输出建立选择列。
void build_tree_columns(TreeColumns &columns, PmuxSelectTree &tree, const std::vector<PmuxEncodedChoice> &networks, const PmuxEncoding &encoding,
			bool specialize)
{
	auto &[roots, output, replaced, all_single, direct_column] = columns;
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
	auto append_column = [&](std::vector<int> values, bool reverse) {
		if (reverse)
			for (int row = 0; row < GetSize(values); ++row)
				if (row < reversed_codes[row])
					std::swap(values[row], values[reversed_codes[row]]);
		roots[reverse].push_back(tree.column(std::move(values), reverse ? reversed_controls : controls));
	};
	for (const auto &network : networks) {
		all_single &= GetSize(network.select) == 1;
		replaced.insert(network.cell);
		output.append(network.y);
		for (int offset = 0; offset < GetSize(network.y); ++offset) {
			std::vector<int> rows(network.rows.size());
			for (int code = 0; code < GetSize(rows); ++code) {
				SigBit bit = network.encoded_data(code, offset);
				auto slot = encoding.slots().find(bit);
				if (slot != encoding.slots().end())
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
}

// 生成一种控制顺序对应的暂存电路，检查收益和删除条件。
std::unique_ptr<PmuxRewrite> tree_candidate(PmuxCoarseIndex &index, PmuxSelectTree &tree, const TreeColumns &columns, const std::vector<int> &roots,
					    const PmuxSelectTree::Analysis &live, const pool<Cell *> &candidates, const char *rule,
					    const std::string &src)
{
	if (columns.all_single && live.mux_bits >= GetSize(columns.output))
		return nullptr;
	auto rewrite = std::make_unique<PmuxRewrite>(index.module, index, rule);
	rewrite->connect(columns.output, tree.emit(&rewrite->staging, roots, src, live));
	if (!rewrite->prepare(candidates, columns.replaced, columns.replaced) ||
	    (!columns.all_single && !columns.direct_column && rewrite->removed.size() == columns.replaced.size()))
		return nullptr;
	return rewrite;
}

// 比较两种控制顺序产生的选择树并校验候选。
std::unique_ptr<PmuxRewrite> rebuild(PmuxCoarseIndex &index, const std::vector<PmuxEncodedChoice> &networks, const PmuxEncoding &encoding,
				     bool specialize)
{
	PmuxSelectTree tree(index, encoding);
	TreeColumns columns;
	build_tree_columns(columns, tree, networks, encoding, specialize);
	const auto &roots = columns.roots;
	pool<Cell *> candidates = encoding.cells();
	candidates.insert(tree.producers.begin(), tree.producers.end());
	const char *rules[2][2] = {
	  {"rebuild_decode", "rebuild_decode_reverse"},
	  {"specialize_decoded_data", "specialize_decoded_data_reverse"},
	};
	auto build_candidate = [&](bool reverse, const PmuxSelectTree::Analysis &live) {
		return tree_candidate(index, tree, columns, roots[reverse], live, candidates, rules[specialize][reverse],
				      networks.front().cell->get_src_attribute());
	};
	auto live = tree.analyze(roots[false]);
	auto forward = build_candidate(false, live);
	if (GetSize(encoding.controls()) <= 1 || roots[true] == roots[false])
		return forward;
	auto reversed_live = tree.analyze(roots[true]);
	if (forward && reversed_live.mux_bits > live.mux_bits)
		return forward;
	auto reverse = build_candidate(true, reversed_live);
	auto rank = [](const PmuxRewrite &rewrite, int count) { return std::pair{count, rewrite.added_count() - GetSize(rewrite.removed)}; };
	if (reverse && (!forward || rank(*reverse, reversed_live.mux_bits) < rank(*forward, live.mux_bits)))
		return reverse;
	return forward;
}

// 估算改写前后的按位逻辑代价差。
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

// 检查额外数据控制位能否通过共享进一步降低代价。
std::unique_ptr<PmuxRewrite> preserve_shared_control(PmuxCoarseIndex &index, const std::vector<PmuxEncodedChoice> &networks,
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
		expanded_networks[pos].rows = std::move(tables[pos]);
	auto rewrite = rebuild(index, expanded_networks, expanded, true);
	if (!rewrite || logic_cost(*rewrite) >= logic_cost(original))
		return nullptr;
	log_debug("PMUX shared_parity_control in %s: selected (gate cost %d -> %d).\n", log_id(index.module), logic_cost(original),
		  logic_cost(*rewrite));
	return rewrite;
}

// 检查未知选择信号下两个分支能否保持原有数据。
dict<Cell *, std::array<bool, 2>> foldable_mux_arms(const std::vector<PmuxEncodedChoice> &networks, const PmuxEncoding &encoding)
{
	std::vector<const PmuxEncodedChoice *> muxes;
	std::vector<Cell *> cells;
	for (const auto &network : networks) {
		if (network.cell->type == ID($mux)) {
			muxes.push_back(&network);
			cells.push_back(network.cell);
		}
	}

	auto choices = encoding.partial_branches(cells);
	const PmuxPartialTable partial(encoding);
	unsigned row_count = partial.row_count;
	auto completions = partial.completions();
	dict<Cell *, std::array<bool, 2>> foldable;
	for (int i = 0; i < GetSize(cells); ++i) {
		uint64_t active = 0;
		for (unsigned code = 0; code < row_count; ++code)
			if (muxes[i]->rows[code] == 1)
				active |= uint64_t(1) << code;
		std::array arms{true, true};
		// 选择位未知时，两个分支各自都需要一个相容的完整编码。
		for (int row = 0; row < GetSize(completions); ++row)
			if (choices[i][row].kind == BranchKind::Dynamic) {
				arms[0] &= (completions[row] & ~active) != 0;
				arms[1] &= (completions[row] & active) != 0;
			}
		foldable.emplace(cells[i], arms);
	}
	return foldable;
}

// 记录沿用原选择信号的输出字段，以及能够直接连接的数据位。
struct FieldPlan {
	Cell *cell;
	SigSpec output, direct_output;
	int first;
};
// 记录同一分支经过不同编码折叠后是否仍为固定节点。
struct BranchChoice {
	enum class Kind { unreachable, fixed, dynamic } kind = Kind::unreachable;
	int value = 0;

	// 将一个编码的结果纳入分支一致性检查。
	void include(int next)
	{
		if (kind == Kind::unreachable)
			*this = {Kind::fixed, next};
		else if (value != next)
			kind = Kind::dynamic;
	}
};
using FoldableArms = std::optional<dict<Cell *, std::array<bool, 2>>>;

// 按完整编码折叠数据位，检查同一分支中的所有结果是否一致。
void fold_branch_data(const PmuxEncodedChoice &network, const std::vector<PmuxEncodedChoice> &networks, const PmuxEncoding &encoding,
		      PmuxSelectTree &tree, FoldableArms &foldable, std::vector<int> &roots, std::vector<FieldPlan> &plans, pool<Cell *> &replaced)
{
	std::vector<std::vector<int>> by_branch(network.branches());
	std::vector<int> direct;
	SigSpec y, direct_y;
	bool changed = false;
	std::vector<BranchChoice> common(network.branches());
	for (int offset = 0; offset < GetSize(network.y); ++offset) {
		std::fill(common.begin(), common.end(), BranchChoice{});
		BranchChoice column;
		for (int code = 0; code < GetSize(network.rows); ++code) {
			int branch = network.rows[code];
			int value = tree.fold(network.bit(branch, offset), code);
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
			int original = tree.literal(network.bit(row, offset));
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
		return;
	plans.push_back({network.cell, y, direct_y, GetSize(roots)});
	for (const auto &branch : by_branch)
		roots.insert(roots.end(), branch.begin(), branch.end());
	roots.insert(roots.end(), direct.begin(), direct.end());
	replaced.insert(network.cell);
}

// 重建分支数据并继续使用原译码信号。
std::unique_ptr<PmuxRewrite> specialize_kept_decode(PmuxCoarseIndex &index, const std::vector<PmuxEncodedChoice> &networks,
						    const PmuxEncoding &encoding, bool shared)
{
	PmuxSelectTree tree(index, encoding);
	std::vector<FieldPlan> plans;
	std::vector<int> roots;
	pool<Cell *> replaced;
	FoldableArms foldable;
	for (const auto &network : networks)
		fold_branch_data(network, networks, encoding, tree, foldable, roots, plans, replaced);
	if (replaced.empty())
		return nullptr;
	auto live = tree.analyze(roots);
	auto rewrite = std::make_unique<PmuxRewrite>(index.module, index, shared ? "specialize_shared_decode" : "specialize_dedicated_decode");
	SigSpec data = tree.emit(&rewrite->staging, roots, networks.front().cell->get_src_attribute(), live);
	for (const auto &plan : plans) {
		auto select = index.port(plan.cell, ID::S);
		int width = GetSize(plan.output);
		int branch_data = width * GetSize(select);
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
	if (!rewrite->prepare(candidates, replaced, replaced) || (!shared && GetSize(rewrite->removed) <= rewrite->added_count()))
		return nullptr;
	return rewrite;
}

// 按名称排序收集形状合法的选择器。
std::vector<IdString> selected_names(Module *module)
{
	std::vector<IdString> names;
	for (auto cell : module->selected_cells())
		if (pmux_select_shape(cell))
			names.push_back(cell->name);
	std::sort(names.begin(), names.end());
	return names;
}

// 按指定的控制条件分组并保持原有遍历顺序。
template <typename Key> std::vector<std::vector<IdString>> group_networks(Module *module, const std::vector<IdString> &names, Key &&key)
{
	dict<SigSpec, int> positions;
	std::vector<std::vector<IdString>> groups;
	for (auto name : names) {
		auto cell = module->cell(name);
		if (!cell)
			continue;
		auto value = key(cell);
		if (!value)
			continue;
		auto [position, inserted] = positions.emplace(std::move(*value), GetSize(groups));
		if (inserted)
			groups.emplace_back();
		groups[position->second].push_back(name);
	}
	std::reverse(groups.begin(), groups.end());
	return groups;
}

enum class Rule { reduce, shared, specialize, rebuild_raw, dedicated };

// 按固定优先级尝试一条规则，复用本组已经计算的译码结果。
std::unique_ptr<PmuxRewrite> try_select_rule(PmuxCoarseIndex &index, Rule rule, const std::vector<PmuxEncodedChoice> &networks,
					     const PmuxEncoding &encoding, const pool<Cell *> &selection_cells, std::optional<bool> &shared_decode)
{
	if (rule == Rule::reduce)
		return reduce_selection_fields(index, networks, encoding);
	if (rule == Rule::shared || rule == Rule::dedicated) {
		if (!shared_decode)
			shared_decode = index.removable(encoding.cells(), selection_cells, {}, {}) != encoding.cells();
		if (*shared_decode == (rule == Rule::shared))
			return specialize_kept_decode(index, networks, encoding, *shared_decode);
		return nullptr;
	}
	auto rewrite = rebuild(index, networks, encoding, rule == Rule::specialize);
	if (rule == Rule::specialize && rewrite) {
		auto shared = preserve_shared_control(index, networks, encoding, *rewrite);
		if (shared)
			return shared;
	}
	return rewrite;
}

// 从当前仍可编辑的选择器收集分支表，必要时合并多组控制编码。
const PmuxEncoding *network_encoding(PmuxCoarseIndex &index, SelectorCache &selectors, const std::vector<IdString> &names, bool pmux_only,
				     std::vector<PmuxEncodedChoice> &networks, pool<Cell *> &selection_cells, std::optional<PmuxEncoding> &combined)
{
	std::vector<SigSpec> select_signals;
	int width = 0;
	for (auto name : names) {
		auto cell = index.module->cell(name);
		if (!cell || !pmux_select_shape(cell) || !index.editable(cell) || (pmux_only && cell->type != ID($pmux)))
			continue;
		const auto &network = networks.emplace_back(index, cell);
		select_signals.push_back(network.select);
		selection_cells.insert(cell);
		width += GetSize(network.y);
	}
	if (networks.empty())
		return nullptr;
	const auto &initial = decode_selector(index, selectors, select_signals.front());
	if (initial.branches.empty())
		return nullptr;
	const PmuxEncoding *encoding = &initial.encoding;
	if (std::all_of(select_signals.begin(), select_signals.end(), [&](const auto &select) { return select == select_signals.front(); })) {
		for (auto &network : networks)
			network.rows = initial.branches;
	} else {
		combined.emplace(initial.encoding);
		encoding = &*combined;
		std::vector<std::vector<int>> tables;
		if (!combined->branch_tables(select_signals, tables))
			return nullptr;
		for (int i = 0; i < GetSize(networks); ++i)
			networks[i].rows = std::move(tables[i]);
	}
	if (width > pmux_max_table_bits / GetSize(networks.front().rows))
		return nullptr;
	return encoding;
}

// 依次尝试各项规则，提交成功后重新读取当前选择网络。
int rewrite_network(PmuxCoarseIndex &index, SelectorCache &selectors, std::vector<IdString> names, bool pmux_only)
{
	const std::array rules{Rule::reduce, Rule::shared, Rule::dedicated, Rule::specialize, Rule::rebuild_raw};
	int rewrites = 0;
	std::vector<PmuxEncodedChoice> networks;
	pool<Cell *> selection_cells;
	std::optional<PmuxEncoding> combined;
	const PmuxEncoding *encoding = nullptr;
	std::optional<bool> shared_decode;
	for (auto rule : rules) {
		if (!encoding) {
			encoding = network_encoding(index, selectors, names, pmux_only, networks, selection_cells, combined);
			if (!encoding)
				break;
		}
		auto rewrite = try_select_rule(index, rule, networks, *encoding, selection_cells, shared_decode);
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
		encoding = nullptr;
		networks.clear();
		selection_cells.clear();
		combined.reset();
		shared_decode.reset();
		selectors.clear();
		++rewrites;
	}
	return rewrites;
}

// 合并外层二选一与内层并行选择器。
int merge_select_wrappers(PmuxCoarseIndex &index)
{
	int rewrites = 0;
	for (auto name : selected_names(index.module)) {
		auto cell = index.module->cell(name);
		if (cell)
			rewrites += merge_wrapper(index, cell);
	}
	return rewrites;
}

// 将控制信号相同的选择器一起处理，无法联合改写时逐个检查。
int rebuild_control_groups(PmuxCoarseIndex &index, SelectorCache &selectors, bool pmux_only)
{
	int rewrites = 0;
	auto groups = group_networks(index.module, selected_names(index.module), [&](Cell *cell) -> std::optional<SigSpec> {
		if ((pmux_only && cell->type != ID($pmux)) || !index.editable(cell))
			return std::nullopt;
		const auto &analysis = decode_selector(index, selectors, index.port(cell, ID::S));
		if (analysis.branches.empty())
			return std::nullopt;
		return analysis.encoding.control_key();
	});
	auto apply = [&](const std::vector<IdString> &names) {
		int changes = rewrite_network(index, selectors, names, pmux_only);
		rewrites += changes;
		return changes != 0;
	};
	for (const auto &names : groups) {
		if (apply(names) || GetSize(names) == 1)
			continue;
		for (const auto &subset : group_networks(index.module, names, [&](Cell *cell) { return std::optional(index.port(cell, ID::S)); })) {
			if (GetSize(subset) > 1 && GetSize(subset) < GetSize(names) && apply(subset))
				continue;
			for (auto name : subset)
				apply({name});
		}
	}
	return rewrites;
}

// 注册控制编码与选择树优化 Pass。
struct OptPmuxSelectPass : Pass {
	// 注册 opt_pmux_select 命令。
	OptPmuxSelectPass() : Pass("opt_pmux_select", "rebuild selection networks from decoded control signals") {}

	// 说明选择树重建及限定并行选择器的选项。
	void help() override
	{
		log("    opt_pmux_select [-pmux-only] [selection]\n\n");
		log("Rebuild mutually exclusive mux selections and specialize their data by control encoding.\n");
		log("-pmux-only restricts rewrite roots to $pmux cells. Private decoder cells may still be removed.\n");
	}

	// 解析选择范围并执行选择器合并和控制分组优化。
	void execute(std::vector<std::string> args, Design *design) override
	{
		bool pmux_only = false;
		size_t argidx = 1;
		for (; argidx < args.size(); ++argidx) {
			if (args[argidx] != "-pmux-only" && args[argidx] != "-pmux_only")
				break;
			pmux_only = true;
		}
		extra_args(args, argidx, design);
		pmux_run_pass(design, "opt_pmux_select", "Executing OPT_PMUX_SELECT pass (rebuild selection networks).\n", [&](Module *module) {
			PmuxCoarseIndex index(module);
			SelectorCache selectors;
			int changes = pmux_only ? 0 : merge_select_wrappers(index);
			return changes + rebuild_control_groups(index, selectors, pmux_only);
		});
	}
} OptPmuxSelectPass;

PRIVATE_NAMESPACE_END

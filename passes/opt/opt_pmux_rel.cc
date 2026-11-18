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

// 优化方法层的输出共享。识别输出之间的异或关系，以及翻转控制位后能够互换的两个通道。

#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

#include <numeric>
#include <ranges>
#include <span>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 表示一个异或表达式的输入集合、反相和未知状态。
struct Parity {
	std::vector<SigBit> terms;
	bool inverted = false, undef = false;

	// 按输入集合、反相及未知状态判定相等。
	bool operator==(const Parity &) const = default;
	// 将异或表达式的各组成部分纳入查找键。
	Hasher hash_into(Hasher hash) const
	{
		hash.eat(terms);
		hash.eat(inverted);
		hash.eat(undef);
		return hash;
	}
};

// 消去两侧共有的异或项，得到两个输出的差异。
Parity difference(const Parity &a, const Parity &b)
{
	if (a.undef || b.undef)
		return {{}, false, true};
	std::vector<SigBit> terms;
	std::set_symmetric_difference(a.terms.begin(), a.terms.end(), b.terms.begin(), b.terms.end(), std::back_inserter(terms));
	return {std::move(terms), a.inverted != b.inverted};
}

// 保存一个输出位在分支与编码行下的值。
template <typename Value> struct ArmColumn {
	std::vector<Value> rows, arms;
	SigBit output;
	int selection;
};

// 记录异或输出的代价和可复用的参考输出。
struct Column : ArmColumn<Parity> {
	int term_count = 0, inversions = 0;
	// 共享来源的选择器编号和输出位偏移。
	std::optional<std::pair<int, int>> reference;
	Parity delta;
};

// 保存选择器视图和各输出列的前驱单元。
struct Selection {
	PmuxChoice table;
	std::vector<Column> columns;
	pool<Cell *> producers;
};

using OperandCache = dict<Cell *, std::pair<SigSpec, SigSpec>>;

// 将单比特信号解释为异或项或常量。
static std::optional<Parity> literal(SigBit bit)
{
	if (bit.wire)
		return Parity{{bit}};
	if (bit == State::S0 || bit == State::S1)
		return Parity{{}, bit == State::S1};
	if (bit == State::Sx)
		return Parity{{}, false, true};
	return std::nullopt;
}

// 沿分支输入提取异或、同或和反相表达式。
std::optional<Parity> arm_parity(PmuxCoarseIndex &index, OperandCache &operators, SigBit bit, pool<Cell *> &region)
{
	auto source = index.source(bit);
	if (!source || source->port != ID::Y || !source->cell->type.in(ID($xor), ID($xnor), ID($not)))
		return literal(bit);
	auto cell = source->cell;
	int width = GetSize(cell->getPort(ID::Y));
	if (width > 4096)
		return literal(bit);
	auto [entry, inserted] = operators.emplace(cell, std::pair<SigSpec, SigSpec>{});
	auto &[lhs, rhs] = entry->second;
	bool unary = cell->type == ID($not);
	if (inserted) {
		bool sign = pmux_cell_signed(cell);
		lhs = index.extended_port(cell, ID::A, width, sign);
		if (!unary)
			rhs = index.extended_port(cell, ID::B, width, sign);
	}
	auto a = literal(lhs[source->offset]);
	auto b = literal(unary ? SigBit(State::S0) : rhs[source->offset]);
	if (!a || !b || (!a->terms.empty() && a->terms == b->terms))
		return literal(bit);
	auto result = difference(*a, *b);
	if (!result.undef)
		result.inverted ^= cell->type != ID($xor);
	region.insert(cell);
	return result;
}

// 检查新表达式是否保留原有的未知值依赖。
static bool preserves_inputs(const Parity &value, const Parity &base, const Parity &delta)
{
	// 保留目标分支的数据依赖，避免为目标引入额外的未定义输入。
	auto includes = [&](const Parity &part) {
		return std::includes(value.terms.begin(), value.terms.end(), part.terms.begin(), part.terms.end());
	};
	return includes(base) && includes(delta);
}

// 将已知的控制位从异或项中移除，同时保留反相和未知状态。
static Parity condition(Parity value, PmuxPartialCode code, const dict<SigBit, int> &slots)
{
	auto output = value.terms.begin();
	for (auto bit : value.terms) {
		auto slot = slots.find(bit);
		if (slot == slots.end()) {
			*output++ = bit;
			continue;
		}
		unsigned mask = 1u << slot->second;
		value.inverted ^= (code.one & mask) != 0;
		value.undef |= ((code.one | code.zero) & mask) == 0;
	}
	value.terms.erase(output, value.terms.end());
	return value;
}

// 逐个检查含未知控制位的编码是否保留输出关系。
static bool partial_relation(const Column &base, const Column &other, const Parity &delta, PmuxPartialTable &partial, const PmuxEncoding &encoding)
{
	const auto &slots = encoding.slots();
	const auto &choices = partial.choices(encoding);
	unsigned full_mask = pmux_encoding_limit(GetSize(slots)) - 1;
	for (int row = 0; row < GetSize(partial.codes); ++row) {
		auto code = partial.codes[row];
		if ((code.one | code.zero) == full_mask)
			continue;
		const auto target = choices[other.selection][row];
		if (target.kind == BranchKind::Undefined) {
			continue;
		}
		bool target_dynamic = target.kind == BranchKind::Dynamic;
		Parity target_a = condition(other.arms[target_dynamic ? 0 : target.index], code, slots);
		Parity target_b;
		if (target_dynamic)
			target_b = condition(other.arms[1], code, slots);
		// 单个 mux 的选择位未知时，任一分支未知都会使结果未知。
		if (target_a.undef || target_b.undef)
			continue;
		const auto source = choices[base.selection][row];
		if (source.kind == BranchKind::Undefined) {
			return false;
		}
		auto matches = [&](int branch) {
			Parity value = condition(base.arms[branch], code, slots);
			auto matches_target = [&](const Parity &expected) {
				return difference(value, expected) == delta && preserves_inputs(expected, value, delta);
			};
			return matches_target(target_a) || (target_dynamic && matches_target(target_b));
		};
		if (source.kind == BranchKind::Dynamic ? !(matches(0) && matches(1)) : !matches(source.index))
			return false;
	}
	return true;
}

// 按预算从选择器的各输出位收集异或表达式。
std::vector<Selection> extract_columns(PmuxCoarseIndex &index, const std::vector<PmuxEncodedChoice> &tables, const dict<SigBit, int> &slots)
{
	OperandCache operators;
	std::vector<Selection> selections;
	const unsigned mask = pmux_encoding_limit(GetSize(slots)) - 1;
	int inspected = 0;
	for (const auto &table : tables) {
		int arms = table.branches();
		int rows = GetSize(table.rows);
		int width = table.width();
		if (width > 4096)
			continue;
		inspected += std::max(rows, arms) * width;
		if (inspected > 65536)
			break;
		auto &selection = selections.emplace_back(Selection{table, {}, {}});
		for (int offset = 0; offset < width; ++offset) {
			auto &column = selection.columns.emplace_back();
			column.output = table.y[offset];
			column.selection = GetSize(selections) - 1;
			for (int arm = 0; arm < arms; ++arm) {
				auto value = arm_parity(index, operators, table.bit(arm, offset), selection.producers);
				if (!value)
					break;
				column.arms.push_back(std::move(*value));
			}
			if (GetSize(column.arms) != arms)
				continue;
			for (auto value : table.map_rows(
			       [&](int row, int arm) { return condition(column.arms[arm], {mask ^ unsigned(row), unsigned(row)}, slots); })) {
				column.term_count += GetSize(value.terms);
				column.inversions += value.inverted;
				column.rows.push_back(std::move(value));
			}
		}
	}
	return selections;
}

// 按各编码行的差异寻找能共享同一个基准的输出列。
template <typename Accept> std::vector<const Column *> solve_relations(std::vector<Selection> &selections, Accept accept)
{
	std::vector<Column *> columns;
	for (auto &selection : selections)
		for (auto &column : selection.columns)
			if (!column.rows.empty())
				columns.push_back(&column);
	std::stable_sort(columns.begin(), columns.end(), [](const Column *a, const Column *b) {
		return std::tie(a->term_count, a->inversions) < std::tie(b->term_count, b->inversions);
	});
	dict<std::vector<Parity>, std::vector<std::pair<const Column *, const Parity *>>> groups;
	std::vector<const Column *> matches;
	for (auto column : columns) {
		auto first = std::find_if(column->rows.begin(), column->rows.end(), [](const Parity &row) { return !row.undef; });
		if (first == column->rows.end())
			continue;
		std::vector<Parity> signature;
		for (const auto &row : column->rows)
			signature.push_back(difference(row, *first));
		auto &bases = groups[signature];
		for (auto [base, value] : bases) {
			auto delta = difference(*value, *first);
			bool usable =
			  std::equal(column->rows.begin(), column->rows.end(), base->rows.begin(),
				     [&](const Parity &row, const Parity &basis) { return row.undef || preserves_inputs(row, basis, delta); });
			if (!usable || !accept(*base, *column, delta))
				continue;
			int offset = base - selections[base->selection].columns.data();
			column->reference.emplace(base->selection, offset);
			column->delta = std::move(delta);
			matches.push_back(column);
			break;
		}
		if (!column->reference && GetSize(bases) < 32)
			bases.emplace_back(column, &*first);
	}
	return matches;
}

// 按异或项数与反相要求，将可共享输出组合成多比特运算。
void emit_parity_relations(PmuxRewrite &rewrite, const std::vector<Selection> &selections, const std::vector<const Column *> &columns)
{
	auto &staging = rewrite.staging;
	// 记录一组可合并为多比特运算的异或输入和输出。
	struct ParityPlan {
		std::vector<SigSpec> operands;
		SigSpec y;
	};
	idict<std::pair<int, bool>> forms;
	std::vector<ParityPlan> relations;
	for (auto column : columns) {
		const auto &delta = column->delta;
		int terms = GetSize(delta.terms);
		int form = forms({terms, delta.inverted});
		if (form == GetSize(relations))
			relations.emplace_back(ParityPlan{std::vector<SigSpec>(terms + 1), {}});
		auto &relation = relations[form];
		auto [selection, offset] = *column->reference;
		relation.operands[0].append(selections[selection].columns[offset].output);
		for (int term = 0; term < terms; ++term)
			relation.operands[term + 1].append(delta.terms[term]);
		relation.y.append(column->output);
	}
	for (int form = GetSize(forms); form-- > 0;) {
		const auto &[terms, inverted] = forms[form];
		const auto &relation = relations[form];
		SigSpec left = relation.operands.front();
		if (!terms) {
			if (inverted)
				staging.addNot(NEW_ID, left, relation.y);
			else
				rewrite.connect(relation.y, left);
			continue;
		}
		for (int term = 1; term <= terms; ++term) {
			bool final = term == terms;
			SigSpec output = final ? relation.y : SigSpec(staging.addWire(NEW_ID, GetSize(relation.y)));
			auto add = final && inverted ? &Module::addXnor : &Module::addXor;
			(staging.*add)(NEW_ID, left, relation.operands[term], output, false, "");
			left = std::move(output);
		}
	}
}

// 保留未配对的输出字段，并校验异或共享电路。
std::unique_ptr<PmuxRewrite> relations(PmuxCoarseIndex &index, const std::vector<Selection> &selections, const std::vector<const Column *> &columns,
				       const pool<Cell *> &producers, const char *rule)
{
	if (columns.empty())
		return nullptr;
	auto rewrite = std::make_unique<PmuxRewrite>(index.module, index, rule);
	auto &staging = rewrite->staging;
	pool<Cell *> candidates, replaced;
	for (const auto &selection : selections) {
		std::vector<int> kept;
		for (int offset = 0; offset < GetSize(selection.columns); ++offset)
			if (!selection.columns[offset].reference)
				kept.push_back(offset);
		if (kept.size() == selection.columns.size())
			continue;
		replaced.insert(selection.table.cell);
		candidates.insert(selection.producers.begin(), selection.producers.end());
		selection.table.emit_slice(staging, kept);
	}
	candidates.insert(replaced.begin(), replaced.end());
	candidates.insert(producers.begin(), producers.end());
	emit_parity_relations(*rewrite, selections, columns);
	return rewrite->prepare(candidates, replaced, replaced) ? std::move(rewrite) : nullptr;
}

using SwapColumn = ArmColumn<int>;

// 表示翻转一个控制位即可互换的两个输出列。
struct SwapPair {
	int first, second;
	std::optional<int> exception;
};

// 检查带有未知选择和例外编码的通道交换。
static bool preserves_partial_swap(const SwapColumn &column, const SwapColumn &other, const std::vector<PmuxBranchChoice> &choices,
				   const std::vector<int> &affected, int low, int high)
{
	for (int row : affected) {
		const auto choice = choices[row];
		if (choice.kind == BranchKind::Undefined) {
			continue;
		}
		// 交换位未知时，局部修正和外层交换可能选中对方在例外编码的数据。
		auto preserves = [&](int value) {
			if (choice.kind == BranchKind::Dynamic)
				return value == column.arms[0] || value == column.arms[1];
			return value == column.arms[choice.index];
		};
		if (!preserves(other.rows[low]) || !preserves(other.rows[high]))
			return false;
	}
	return true;
}

// 用各编码行的数据匹配可交换的输出列。
struct SwapSignature {
	std::span<const int> values;
	std::optional<std::pair<int, int>> exception;
	int flip;
	Hasher::hash_t fingerprint;

	// 按指定翻转方向计算参与匹配的编码行指纹。
	SwapSignature(const std::vector<int> &values, std::optional<std::pair<int, int>> exception, int flip)
	    : values(values), exception(exception), flip(flip)
	{
		Hasher hash;
		for (int row = 0; row < GetSize(values); ++row)
			if (!ignored(row))
				hash.eat(values[row ^ flip]);
		fingerprint = hash.yield();
	}

	// 检查当前编码是否属于需要单独处理的例外。
	bool ignored(int row) const { return exception && (row == exception->first || row == exception->second); }

	// 逐行比较相同指纹对应的有效数据。
	bool operator==(const SwapSignature &other) const
	{
		if (fingerprint != other.fingerprint || exception != other.exception || values.size() != other.values.size())
			return false;
		for (int row = 0; row < GetSize(values); ++row)
			if (!ignored(row) && values[row ^ flip] != other.values[row ^ other.flip])
				return false;
		return true;
	}

	// 使用已计算的行指纹查找候选输出列。
	Hasher hash_into(Hasher hash) const
	{
		hash.eat(fingerprint);
		return hash;
	}
};

// 找到交换控制位未确定且与例外编码相容的三态行。
std::vector<int> affected_rows(const PmuxPartialTable &partial, int mask, int candidate)
{
	std::vector<int> affected;
	for (int row = 0; row < GetSize(partial.codes); ++row) {
		const auto &code = partial.codes[row];
		unsigned fixed = code.zero | code.one;
		if (!(fixed & mask) && (unsigned(candidate) & fixed) == code.one)
			affected.push_back(row);
	}
	return affected;
}

// 在搜索预算内寻找能够按控制位互换的输出列。
template <typename Accept>
bool match_swap_columns(const std::vector<SwapColumn> &columns, int mask, std::optional<std::pair<int, int>> except, std::vector<bool> &used,
			std::vector<SwapPair> &pairs, Accept accept)
{
	dict<SwapSignature, std::vector<int>> groups;
	for (int col = 0; col < GetSize(columns); ++col)
		if (!used[col])
			groups[SwapSignature(columns[col].rows, except, 0)].push_back(col);

	for (int col = 0; col < GetSize(columns); ++col) {
		if (used[col])
			continue;
		const auto &a = columns[col];
		auto partners = groups.find(SwapSignature(a.rows, except, mask));
		if (partners == groups.end() || (!except && std::binary_search(partners->second.begin(), partners->second.end(), col)))
			continue;
		for (int partner : partners->second) {
			if (partner == col || used[partner])
				continue;
			const auto &b = columns[partner];
			auto accepted = accept(a, b);
			if (!accepted)
				return false;
			if (!*accepted)
				continue;
			used[col] = true;
			used[partner] = true;
			pairs.push_back({col, partner, except ? std::optional(except->first) : std::nullopt});
			break;
		}
	}
	return true;
}

// 在全部编码上查找直接交换的输出列。
std::vector<SwapPair> exact_swap_pairs(const std::vector<SwapColumn> &columns, int mask)
{
	std::vector<SwapPair> pairs;
	std::vector<bool> used(columns.size());
	match_swap_columns(columns, mask, {}, used, pairs, [](const auto &, const auto &) { return std::optional(true); });
	return pairs;
}

// 排除已经完全互换的列，并检查例外编码在未知选择下的结果。
bool compatible_exception(const SwapColumn &a, const SwapColumn &b, int low, int high, const std::vector<int> &affected, PmuxPartialTable &partial,
			  const PmuxEncoding &encoding)
{
	if (a.rows[low] == b.rows[high] && a.rows[high] == b.rows[low])
		return false;
	const auto &branches = partial.choices(encoding);
	return preserves_partial_swap(a, b, branches[a.selection], affected, low, high) &&
	       preserves_partial_swap(b, a, branches[b.selection], affected, low, high);
}

// 允许在一对编码上补充选择逻辑，逐个验证受影响的三态编码。
std::vector<SwapPair> corrected_swap_pairs(const std::vector<SwapColumn> &columns, int mask, PmuxPartialTable &partial, const PmuxEncoding &encoding)
{
	std::vector<SwapPair> pairs;
	std::vector<bool> used(columns.size());
	int budget = pmux_max_pair_checks;
	int rows = GetSize(columns.front().rows);
	for (int low = 0; low < rows; ++low) {
		if (low & mask)
			continue;
		int high = low | mask;
		auto affected = affected_rows(partial, mask, low);
		auto accept = [&](const SwapColumn &a, const SwapColumn &b) -> std::optional<bool> {
			budget -= 1 + GetSize(affected);
			if (budget < 0)
				return std::nullopt;
			return compatible_exception(a, b, low, high, affected, partial, encoding);
		};
		if (!match_swap_columns(columns, mask, std::pair(low, high), used, pairs, accept))
			break;
	}
	return pairs;
}

// 收集配对通道的新选择树节点，并记录各选择器仍需保留的输出。
struct SwapPlan {
	pool<Cell *> replaced;
	std::vector<int> roots, reference;
	std::vector<std::vector<int>> offsets;
	SigSpec swap_y;
	bool shares_selection = false;
};

// 生成交换前的一列数据，在例外编码中保留配对通道的原值。
int shared_swap_column(PmuxSelectTree &tree, const SwapColumn &first, const SwapColumn &second, int mask, const SwapPair &pair,
		       const std::vector<int> &controls, bool &shares_selection)
{
	std::vector<int> values;
	for (int row = 0; row < GetSize(first.rows); ++row) {
		if (row & mask)
			continue;
		values.push_back(first.rows[row]);
		if (pair.exception)
			values.push_back(row == *pair.exception ? second.rows[row | mask] : first.rows[row]);
	}
	shares_selection |= std::adjacent_find(values.begin(), values.end(), std::not_equal_to<int>{}) != values.end();
	return tree.column(std::move(values), controls);
}

// 为每对通道生成共用子树和外层交换节点。
void build_swap_nodes(SwapPlan &plan, const std::vector<PmuxEncodedChoice> &tables, const PmuxEncoding &encoding, PmuxSelectTree &tree,
		      const std::vector<SwapColumn> &columns, const std::vector<int> &starts, int flip, const std::vector<SwapPair> &pairs)
{
	auto &[replaced, roots, reference, offsets, swap_y, shares_selection] = plan;
	offsets.resize(tables.size());
	std::vector<int> controls, natural_order;
	if (!pairs.empty() && pairs.front().exception)
		controls.push_back(flip);
	for (int control = 0; control < GetSize(encoding.controls()); ++control) {
		natural_order.push_back(control);
		if (control != flip)
			controls.push_back(control);
	}
	int mask = 1 << flip;
	for (const auto &pair : pairs) {
		const auto &a = columns[pair.first];
		const auto &b = columns[pair.second];
		int left = shared_swap_column(tree, a, b, mask, pair, controls, shares_selection);
		int right = shared_swap_column(tree, b, a, mask, pair, controls, shares_selection);
		int level = GetSize(controls);
		roots.push_back(tree.select(flip, level, left, right));
		roots.push_back(tree.select(flip, level, right, left));
		for (int column : {pair.first, pair.second}) {
			const auto &entry = columns[column];
			if (pair.exception)
				reference.push_back(tree.column(entry.rows, natural_order));
			swap_y.append(entry.output);
			replaced.insert(tables[entry.selection].cell);
			offsets[entry.selection].push_back(column - starts[entry.selection]);
		}
	}
}

// 检查共享选择树的代价，为未配对的输出生成保留切片。
std::unique_ptr<PmuxRewrite> swap_outputs(PmuxCoarseIndex &index, const std::vector<PmuxEncodedChoice> &tables, const PmuxEncoding &encoding,
					  PmuxSelectTree &tree, const std::vector<SwapColumn> &columns, const std::vector<int> &starts, int flip,
					  const std::vector<SwapPair> &pairs)
{
	SwapPlan plan;
	build_swap_nodes(plan, tables, encoding, tree, columns, starts, flip, pairs);
	auto &[replaced, roots, reference, offsets, swap_y, shares_selection] = plan;
	if (roots.empty())
		return nullptr;
	auto live = tree.analyze(roots);
	bool shared_control = std::all_of(tables.begin(), tables.end(),
					  [&](const auto &table) { return table.cell->type == ID($mux) && table.select == tables.front().select; });
	if (reference.empty() && shared_control && live.mux_bits > GetSize(swap_y))
		return nullptr;
	if (!reference.empty() && live.mux_bits >= tree.analyze(reference).mux_bits)
		return nullptr;
	auto rewrite = std::make_unique<PmuxRewrite>(index.module, index, "encoded_output_swap");
	auto &staging = rewrite->staging;
	rewrite->connect(swap_y, tree.emit(&staging, roots, tables.front().cell->get_src_attribute(), live));
	bool combines_selections = GetSize(replaced) > 1;
	for (int pos = 0; pos < GetSize(tables); ++pos) {
		if (offsets[pos].empty())
			continue;
		auto &skip = offsets[pos];
		std::sort(skip.begin(), skip.end());
		std::vector<int> kept;
		for (int offset = 0; offset < tables[pos].width(); ++offset)
			if (!std::binary_search(skip.begin(), skip.end(), offset))
				kept.push_back(offset);
		combines_selections &= kept.empty();
		tables[pos].emit_slice(staging, kept);
	}
	pool<Cell *> candidates = encoding.cells();
	candidates.insert(replaced.begin(), replaced.end());
	candidates.insert(tree.producers.begin(), tree.producers.end());
	rewrite->find_removable(candidates, replaced);
	bool removes_selection_logic =
	  std::any_of(rewrite->removed.begin(), rewrite->removed.end(), [&](auto cell) { return !replaced.count(cell) || cell->type == ID($pmux); });
	if ((!shares_selection && !combines_selections && !removes_selection_logic) ||
	    !std::all_of(replaced.begin(), replaced.end(), [&](auto cell) { return rewrite->removed.count(cell); }) || !rewrite->validate())
		return nullptr;
	return rewrite;
}

// 提交通过验证的候选并返回是否发生改写。
bool apply(std::unique_ptr<PmuxRewrite> rewrite)
{
	if (!rewrite)
		return false;
	rewrite->commit();
	return true;
}

// 按原有名称顺序重新查找仍然可编辑的选择器。
std::vector<Cell *> live_cells(PmuxCoarseIndex &index, const std::vector<IdString> &names)
{
	std::vector<Cell *> result;
	for (auto name : names) {
		auto cell = index.module->cell(name);
		if (cell && pmux_select_shape(cell) && index.editable(cell))
			result.push_back(cell);
	}
	return result;
}

// 按稳定顺序收集形状合法的选择器。
std::vector<Cell *> selected_choices(PmuxCoarseIndex &index)
{
	auto cells = index.module->selected_cells();
	cells.erase(std::remove_if(cells.begin(), cells.end(), [&](auto cell) { return !pmux_select_shape(cell) || !index.editable(cell); }),
		    cells.end());
	std::sort(cells.begin(), cells.end(), [](auto a, auto b) { return a->name < b->name; });
	return cells;
}

// 依次尝试无例外和单组例外编码下的输出交换。
bool rewrite_swap(PmuxCoarseIndex &index, const PmuxEncoding &encoding, const std::vector<PmuxEncodedChoice> &tables)
{
	int rows = GetSize(tables.front().rows);
	int controls = GetSize(encoding.controls());
	for (bool allow_exception : {false, true}) {
		if (allow_exception && controls < 3)
			break;
		PmuxSelectTree tree(index, encoding);
		std::vector<SwapColumn> columns;
		std::vector<int> starts;
		std::optional<PmuxPartialTable> partial;
		if (allow_exception)
			partial.emplace(encoding);
		for (const auto &table : tables) {
			int width = table.width();
			if (GetSize(columns) + width > pmux_max_table_bits / rows)
				break;
			int selection = GetSize(starts);
			starts.push_back(GetSize(columns));
			if (partial)
				partial->cells.push_back(table.cell);
			for (int offset = 0; offset < width; ++offset) {
				auto &column = columns.emplace_back(SwapColumn{{}, {}, table.y[offset], selection});
				if (partial)
					for (int arm = 0; arm < table.branches(); ++arm)
						column.arms.push_back(tree.literal(table.bit(arm, offset)));
				auto values = table.map_rows(
				  [&](int row, int arm) { return partial ? column.arms[arm] : tree.fold(table.bit(arm, offset), row); });
				for (int value : values)
					column.rows.push_back(value);
			}
		}
		if (GetSize(columns) < 2)
			return false;
		for (int flip = 0; flip < controls; ++flip) {
			auto pairs = partial ? corrected_swap_pairs(columns, 1 << flip, *partial, encoding) : exact_swap_pairs(columns, 1 << flip);
			if (apply(swap_outputs(index, tables, encoding, tree, columns, starts, flip, pairs)))
				return true;
		}
	}
	return false;
}

// 在同一组控制变量下为多个选择器建立分支映射。
std::vector<PmuxEncodedChoice> encoded_tables(PmuxCoarseIndex &index, const std::vector<IdString> &names, PmuxEncoding &encoding)
{
	std::vector<PmuxEncodedChoice> tables;
	std::vector<SigSpec> selects;
	for (auto cell : live_cells(index, names))
		selects.push_back(tables.emplace_back(index, cell).select);
	std::vector<std::vector<int>> rows;
	if (!encoding.branch_tables(selects, rows))
		return {};
	for (int i = 0; i < GetSize(rows); ++i)
		tables[i].rows = std::move(rows[i]);
	return tables;
}

// 共享使用完全相同选择信号的异或与反相输出。
int share_exact_relations(PmuxCoarseIndex &index)
{
	idict<std::pair<IdString, SigSpec>> keys;
	std::vector<std::vector<IdString>> exact;
	for (auto cell : selected_choices(index)) {
		SigSpec select = index.port(cell, ID::S);
		if (GetSize(select) > 32)
			continue;
		int group = keys({cell->type, select});
		if (group == GetSize(exact))
			exact.emplace_back();
		exact[group].push_back(cell->name);
	}
	int changes = 0;
	for (int group = GetSize(exact); group-- > 0;) {
		auto control = index.sigmap(keys[group].second);
		std::vector<PmuxEncodedChoice> tables;
		for (auto cell : live_cells(index, exact[group]))
			if (index.port(cell, ID::S) == control) {
				auto &choice = tables.emplace_back(index, cell);
				choice.rows.resize(choice.branches());
				std::iota(choice.rows.begin(), choice.rows.end(), 0);
			}
		auto selections = extract_columns(index, tables, {});
		auto matches = solve_relations(selections, [](const auto &, const auto &, const auto &) { return true; });
		changes += apply(relations(index, selections, matches, {}, "output_relation"));
	}
	return changes;
}

// 比较编码分组中的输出共享和通道交换机会。
int rewrite_encoded_group(PmuxCoarseIndex &index, std::vector<IdString> &names)
{
	PmuxEncoding encoding(index);
	auto tables = encoded_tables(index, names, encoding);
	if (tables.empty())
		return 0;
	auto selections = extract_columns(index, tables, encoding.slots());
	std::optional<PmuxPartialTable> partial;
	auto accept = [&](const Column &base, const Column &target, const Parity &delta) {
		if (!partial) {
			partial.emplace(encoding);
			for (const auto &selection : selections)
				partial->cells.push_back(selection.table.cell);
		}
		return partial_relation(base, target, delta, *partial, encoding);
	};
	auto matches = solve_relations(selections, accept);
	auto rewrite = relations(index, selections, matches, encoding.cells(), "encoded_output_relation");
	if (!rewrite)
		return rewrite_swap(index, encoding, tables);
	for (auto cell : rewrite->staging.cells())
		if (pmux_select_shape(cell))
			names.push_back(cell->name);
	rewrite->commit();
	PmuxEncoding updated(index);
	auto updated_tables = encoded_tables(index, names, updated);
	return 1 + (!updated_tables.empty() && rewrite_swap(index, updated, updated_tables));
}

// 按控制编码分组后依次尝试异或共享和通道交换。
int share_encoded_relations(PmuxCoarseIndex &index)
{
	int changes = 0;
	idict<SigSpec> keys;
	std::vector<std::vector<IdString>> encoded;
	for (auto cell : selected_choices(index)) {
		PmuxEncoding encoding(index);
		std::vector<int> rows;
		if (!encoding.branch_table(index.port(cell, ID::S), rows))
			continue;
		int group = keys(encoding.control_key());
		if (group == GetSize(encoded))
			encoded.emplace_back();
		encoded[group].push_back(cell->name);
	}
	for (int group = GetSize(encoded); group-- > 0;)
		changes += rewrite_encoded_group(index, encoded[group]);
	return changes;
}

// 注册选择器输出关系共享 Pass。
struct OptPmuxRelPass : Pass {
	// 注册 opt_pmux_rel 命令。
	OptPmuxRelPass() : Pass("opt_pmux_rel", "share identical, complementary, and XOR-related selection outputs") {}

	// 说明异或共享、控制位交换及例外编码。
	void help() override
	{
		log("    opt_pmux_rel [selection]\n\n");
		log("Share selection outputs related by a fixed XOR or a swap under one control bit.\n");
		log("A swap can have one exceptional pair of encodings, corrected by local muxes.\n");
	}

	// 依次处理选择信号相同和控制编码相同的分组。
	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		pmux_run_pass(design, "opt_pmux_rel", "Executing OPT_PMUX_REL pass.\n", [&](Module *module) {
			PmuxCoarseIndex index(module);
			int changes = share_exact_relations(index);
			return changes + share_encoded_relations(index);
		});
	}
} OptPmuxRelPass;

PRIVATE_NAMESPACE_END

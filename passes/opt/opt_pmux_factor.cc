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

// 优化方法层的公共运算提取。识别选择分支中重复的运算、操作数和归约表达式。

#include "kernel/log.h"
#include "kernel/register.h"
#include "passes/opt/pmux_common.h"
#include "passes/opt/pmux_rewrite.h"

#include <algorithm>
#include <array>
#include <map>
#include <optional>
#include <set>
#include <span>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// 记录分支数据位及其前驱运算和输入。
struct FactorBit {
	SigBit value;
	Cell *producer = nullptr;
	SigBit a, b, select;
};

// 表示能够从多个选择分支中共同提取的输出字段。
struct FactorField {
	enum class Input { FixedOperands, SelectedOperand, SelectedControl };
	Input input = Input::FixedOperands;
	IdString type;
	std::vector<int> offsets;
	SigSpec a, b;
	std::vector<SigSpec> branches;
	pool<IdString> producers;

	// 记录一个匹配的数据位及参与提取的前驱。
	void append(int offset, SigBit left, const pool<IdString> &cells)
	{
		offsets.push_back(offset);
		a.append(left);
		producers.insert(cells.begin(), cells.end());
	}

	// 生成公共运算，并为各分支间不同的操作数构造选择。
	SigSpec emit(Module *module, const SigSpec &select) const
	{
		auto operand = input == Input::FixedOperands ? b : pmux_build_choice(module, select, branches);
		if (input == Input::SelectedControl)
			return module->Mux(NEW_ID, a, b, operand);
		return pmux_emit_bitwise_choice(module, type, a, operand);
	}
};

// 枚举未知选择信号下的输入，检查提取前后的确定值。
bool preserves_unknown_select(IdString type, const SigSpec &a, const SigSpec &b)
{
	// $mux 在选择未知时逐位合并两路结果。枚举叶子取值，并让相同信号共享赋值。
	std::array<SigBit, 4> inputs = {a[0], b[0], a[1], b[1]};
	dict<SigBit, int> weights;
	int count = 1;
	for (auto bit : inputs)
		if (bit.wire && weights.emplace(bit, count).second)
			count *= 3;
	for (int code = 0; code < count; ++code) {
		auto value = [&](SigBit bit) {
			static constexpr std::array<State, 3> states{State::S0, State::S1, State::Sx};
			return bit.wire ? states[code / weights.at(bit) % 3] : bit.data;
		};
		auto a0 = value(inputs[0]);
		auto b0 = value(inputs[1]);
		auto a1 = value(inputs[2]);
		auto b1 = value(inputs[3]);
		auto first = pmux_eval_bitwise(type, a0, b0);
		if (first != State::Sx && first == pmux_eval_bitwise(type, a1, b1) &&
		    first != pmux_eval_bitwise(type, a0 == a1 ? a0 : State::Sx, b0 == b1 ? b0 : State::Sx))
			return false;
	}
	return true;
}

// 按分支数据索引已有的选择器输出列。
struct ChoiceColumns {
	// 记录各分支的数据及其对应的现有输出位。
	struct Column {
		SigSpec values;
		SigBit output;
	};
	std::vector<Column> columns;
	std::vector<dict<SigBit, std::vector<int>>> by_branch;
	dict<SigSpec, std::vector<int>> exact, without_default;
};

// 汇总同类前驱，保留可选输出列最少的分支以限制后续搜索。
bool reusable_sources(const std::vector<FactorBit> &bits, const ChoiceColumns &available, int first, IdString type,
		      std::array<const std::vector<int> *, 2> &candidates, pool<IdString> &producers)
{
	int fewest = GetSize(available.columns) + 1;
	for (int branch = first; branch < GetSize(bits); ++branch) {
		const auto &bit = bits[branch];
		if (!bit.producer || bit.producer->type != type)
			return false;
		producers.insert(bit.producer->name);
		const auto &row = available.by_branch[branch];
		auto left = row.find(bit.a);
		auto right = row.find(bit.b);
		int size = (left == row.end() ? 0 : GetSize(left->second)) + (right == row.end() || bit.a == bit.b ? 0 : GetSize(right->second));
		if (size < fewest) {
			fewest = size;
			candidates = {left == row.end() ? nullptr : &left->second, right == row.end() || bit.a == bit.b ? nullptr : &right->second};
		}
	}
	return true;
}

// 在各分支中去除已匹配的操作数，收集另一侧的操作数。
SigSpec other_operands(const std::vector<FactorBit> &bits, const ChoiceColumns::Column &left, int first)
{
	SigSpec values;
	for (int branch = first; branch < GetSize(bits); ++branch) {
		const auto &bit = bits[branch];
		if (left.values[branch] != bit.a && left.values[branch] != bit.b)
			break;
		values.append(left.values[branch] == bit.a ? bit.b : bit.a);
	}
	return values;
}

// 为仅找到一个可复用操作数的输出位记录余下的选择逻辑。
void append_single_operand(FactorField &field, IdString type, int offset, SigBit existing_operand, const pool<IdString> &producers,
			   const std::vector<FactorBit> &bits, int first, const SigSpec &missing_operand)
{
	field.input = FactorField::Input::SelectedOperand;
	field.type = type;
	field.append(offset, existing_operand, producers);
	field.branches.resize(bits.size());
	for (int branch = 0; branch < GetSize(bits); ++branch)
		field.branches[branch].append(branch < first ? SigBit(State::Sx) : missing_operand[branch - first]);
}

// 尝试复用一对现成的输出列，并排除会产生组合环路的连接。
bool reuse_operand_pair(PmuxCoarseIndex &index, const std::vector<int> &matches, const ChoiceColumns &available, const pool<SigBit> &outputs,
			SigBit left, int offset, IdString type, const pool<IdString> &producers, std::map<IdString, FactorField> &reused)
{
	for (int other : matches) {
		SigBit right = available.columns[other].output;
		if (outputs.count(right) || !index.independent({left, right}, outputs))
			continue;
		auto &field = reused[type];
		field.type = type;
		field.append(offset, left, producers);
		field.b.append(right);
		return true;
	}
	return false;
}

// 查找能够复用一侧或两侧选择结果的公共运算。
void match_reusable_field(PmuxCoarseIndex &index, Cell *root, const pool<SigBit> &outputs, int offset, const std::vector<FactorBit> &bits,
			  const ChoiceColumns &available, std::map<IdString, FactorField> &reused, std::map<IdString, FactorField> &single_operand)
{
	bool ignore_default = root->type == ID($pmux) && bits.front().value == State::Sx;
	int first = ignore_default ? 1 : 0;
	if (!bits[first].producer || bits[first].producer->type == ID($mux))
		return;
	IdString type = bits[first].producer->type;
	std::array<const std::vector<int> *, 2> candidates{};
	pool<IdString> producers;
	if (!reusable_sources(bits, available, first, type, candidates, producers))
		return;

	SigBit existing_operand;
	SigSpec missing_operand;
	const auto &lookup = ignore_default ? available.without_default : available.exact;
	for (const auto *row : candidates) {
		if (!row)
			continue;
		for (int column : *row) {
			const auto &left = available.columns[column];
			if (outputs.count(left.output))
				continue;
			auto values = other_operands(bits, left, first);
			if (GetSize(values) != GetSize(bits) - first)
				continue;
			if (root->type == ID($mux) && !preserves_unknown_select(type, left.values, values))
				continue;
			auto matching = lookup.find(values);
			if (matching != lookup.end() &&
			    reuse_operand_pair(index, matching->second, available, outputs, left.output, offset, type, producers, reused))
				return;
			if (!existing_operand.wire) {
				pool<SigBit> inputs(values.begin(), values.end());
				inputs.insert(left.output);
				if (index.independent(inputs, outputs)) {
					existing_operand = left.output;
					missing_operand = std::move(values);
				}
			}
		}
	}
	if (existing_operand.wire)
		append_single_operand(single_operand[type], type, offset, existing_operand, producers, bits, first, missing_operand);
}

// 识别各分支中拥有相同数据输入的二选一单元。
void match_nested_fields(int offset, const std::vector<FactorBit> &bits, std::map<std::vector<SigBit>, FactorField> &fields)
{
	for (const auto &seed : bits) {
		if (!seed.producer || seed.producer->type != ID($mux))
			continue;
		std::vector<SigBit> conditions;
		pool<IdString> producers;
		for (const auto &branch : bits) {
			if (branch.value == State::Sx) {
				conditions.emplace_back(State::Sx);
			} else if (branch.value == seed.a || branch.value == seed.b) {
				conditions.emplace_back(branch.value == seed.a ? State::S0 : State::S1);
			} else if (branch.producer && branch.producer->type == ID($mux) && branch.a == seed.a && branch.b == seed.b) {
				conditions.push_back(branch.select);
				producers.insert(branch.producer->name);
			} else
				break;
		}
		if (conditions.size() != bits.size() || producers.empty())
			continue;
		auto &field = fields[conditions];
		if (field.offsets.empty()) {
			field.input = FactorField::Input::SelectedControl;
			field.type = ID($mux);
			for (auto condition : conditions)
				field.branches.emplace_back(condition);
		}
		field.append(offset, seed.a, producers);
		field.b.append(seed.b);
		break;
	}
}

// 检查分支运算能否共享指定操作数。
bool match_bitwise_field(FactorField &field, int offset, const std::vector<FactorBit> &bits, SigBit common)
{
	std::vector<SigBit> operands;
	pool<IdString> producers;
	for (const auto &branch : bits) {
		if (branch.value == State::Sx) {
			operands.push_back(branch.value);
			continue;
		}
		if (branch.value == common) {
			operands.emplace_back(field.type.in(ID($and), ID($xnor)) ? State::S1 : State::S0);
			continue;
		}
		if (!branch.producer || branch.producer->type != field.type || (branch.a != common && branch.b != common))
			return false;
		operands.push_back(branch.a == common ? branch.b : branch.a);
		producers.insert(branch.producer->name);
	}
	if (producers.empty())
		return false;
	field.append(offset, common, producers);
	field.branches.resize(operands.size());
	for (int i = 0; i < GetSize(operands); ++i)
		field.branches[i].append(operands[i]);
	return true;
}

// 依次尝试两个操作数作为公共输入。
void match_bitwise_fields(int offset, const std::vector<FactorBit> &bits, std::array<std::map<IdString, FactorField>, 2> &fields)
{
	pool<IdString> matched_types;
	for (const auto &seed : bits) {
		if (!seed.producer || seed.producer->type == ID($mux) || !matched_types.insert(seed.producer->type).second)
			continue;
		for (int variant = 0; variant < GetSize(fields); ++variant) {
			auto &field = fields[variant][seed.producer->type];
			field.input = FactorField::Input::SelectedOperand;
			field.type = seed.producer->type;
			if (!match_bitwise_field(field, offset, bits, variant == 0 ? seed.a : seed.b) && seed.a != seed.b)
				match_bitwise_field(field, offset, bits, variant == 0 ? seed.b : seed.a);
		}
	}
}

// 逐位读取各分支的前驱并收集可提取字段。
template <typename Match> void match_choice_fields(PmuxCoarseIndex &index, const std::vector<SigSpec> &branches, Match match)
{
	// 缓存同一运算单元的扩展操作数与控制信号。
	struct Inputs {
		SigSpec a, b;
		SigBit select;
	};
	dict<Cell *, Inputs> drivers;
	std::vector<FactorBit> bits;
	for (int offset = 0; offset < GetSize(branches.front()); ++offset) {
		bits.clear();
		for (const auto &branch : branches) {
			auto bit = branch[offset];
			auto source = index.source(bit);
			if (!source || source->port != ID::Y || !source->cell->type.in(ID($mux), ID($and), ID($or), ID($xor), ID($xnor))) {
				bits.push_back({bit, nullptr, {}, {}, {}});
				continue;
			}
			auto cell = source->cell;
			auto [entry, inserted] = drivers.emplace(cell, Inputs{});
			auto &[a, b, select] = entry->second;
			if (inserted) {
				a = index.port(cell, ID::A);
				b = index.port(cell, ID::B);
				if (cell->type == ID($mux))
					select = index.port(cell, ID::S).as_bit();
				else {
					bool sign = pmux_cell_signed(cell);
					int width = GetSize(cell->getPort(ID::Y));
					a.extend_u0(width, sign);
					b.extend_u0(width, sign);
				}
			}
			bits.push_back({bit, cell, a[source->offset], b[source->offset], select});
		}
		match(offset, bits);
	}
}

// 记录一个待改写选择器的分支和提取字段。
struct ChoiceRewrite {
	Cell *root;
	std::span<const SigSpec> branches;
	std::vector<FactorField> fields;
};

// 按既定优先顺序选取字段，每个输出位只参与一次提取。
template <typename Range, typename Field>
void select_fields(const Range &range, Field field_of, pool<int> &occupied, std::vector<FactorField> &selected)
{
	for (const auto &entry : range) {
		const auto &field = field_of(entry);
		if (field.offsets.empty() ||
		    std::any_of(field.offsets.begin(), field.offsets.end(), [&](int offset) { return occupied.count(offset); }))
			continue;
		occupied.insert(field.offsets.begin(), field.offsets.end());
		selected.push_back(field);
	}
}

// 构造公共运算和剩余选择位并检查删除收益。
bool apply_factor(PmuxCoarseIndex &index, const std::vector<ChoiceRewrite> &edits, const char *rule, bool require_reduction,
		  IdString *remaining_choice = nullptr)
{
	PmuxRewrite rewrite(index.module, index, rule);
	pool<Cell *> region;
	IdString residual;
	for (const auto &[root, branches, fields] : edits) {
		region.insert(root);
		auto output = root->getPort(ID::Y);
		auto select = index.port(root, ID::S);
		pool<int> factored;
		for (const auto &field : fields) {
			for (auto name : field.producers) {
				auto cell = index.module->cell(name);
				if (cell)
					region.insert(cell);
			}
			SigSpec field_output;
			for (int offset : field.offsets) {
				log_assert(factored.insert(offset).second);
				field_output.append(output[offset]);
			}
			rewrite.connect(field_output, field.emit(&rewrite.staging, select));
		}
		std::vector<int> kept;
		for (int offset = 0; offset < GetSize(output); ++offset)
			if (!factored.count(offset))
				kept.push_back(offset);
		if (kept.empty())
			continue;

		// 保留各个分支在这些输出位置的数据，公共分支可直接连接。
		std::vector<SigSpec> remaining;
		for (const auto &branch : branches)
			remaining.push_back(pmux_slice(branch, kept));
		rewrite.connect(pmux_slice(output, kept), pmux_build_choice(&rewrite.staging, select, remaining, root->type, &residual));
	}
	rewrite.find_removable(region);
	if (require_reduction && GetSize(rewrite.removed) <= rewrite.added_count())
		return false;
	for (const auto &edit : edits)
		for (const auto &field : edit.fields)
			if (std::none_of(field.producers.begin(), field.producers.end(),
					 [&](IdString name) { return rewrite.removed.count(index.module->cell(name)); }))
				return false;
	if (!rewrite.validate())
		return false;
	rewrite.commit();
	if (remaining_choice)
		*remaining_choice = residual;
	return true;
}

// 按已识别的优先顺序尝试局部字段组合。
template <typename Maps>
bool factor_local_fields(PmuxCoarseIndex &index, Cell *root, const std::vector<SigSpec> &branches, const Maps &matches, const char *rule,
			 IdString *remaining_choice = nullptr)
{
	auto apply = [&](const std::vector<FactorField> &fields) {
		return apply_factor(index, {{root, branches, fields}}, rule, false, remaining_choice);
	};
	std::vector<FactorField> single_fields;
	for (const auto &variant : matches) {
		std::vector<FactorField> fields;
		pool<int> occupied;
		select_fields(variant, [](const auto &entry) -> const auto & { return entry.second; }, occupied, fields);
		for (const auto &[type, field] : variant)
			if (!field.offsets.empty())
				single_fields.push_back(field);
		if (GetSize(fields) > 1 && apply(fields))
			return true;
	}
	for (const auto &field : single_fields)
		if (apply({field}))
			return true;
	return false;
}

// 收集选中模块内可参与提取的选择器名称。
std::vector<IdString> selected_choices(Module *module)
{
	std::vector<IdString> choices;
	for (auto cell : module->selected_cells())
		if (pmux_has_selection_port(cell, ID::S) && !cell->getPort(ID::S).empty())
			choices.push_back(cell->name);
	std::sort(choices.begin(), choices.end());
	return choices;
}

// 在单个选择器内提取公共的按位或嵌套选择运算。
int factor_local_choices(PmuxCoarseIndex &index)
{
	int rewrites = 0;
	for (auto name : selected_choices(index.module)) {
		auto root = index.module->cell(name);
		if (!root || !index.editable(root))
			continue;
		auto branches = PmuxChoice(index, root).all_arms();
		std::array<std::map<std::vector<SigBit>, FactorField>, 1> nested;
		match_choice_fields(index, branches, [&](int offset, const auto &bits) { match_nested_fields(offset, bits, nested.front()); });
		IdString remaining_choice;
		if (factor_local_fields(index, root, branches, nested, "factor nested selections", &remaining_choice)) {
			++rewrites;
			if (remaining_choice.empty())
				continue;
			root = index.module->cell(remaining_choice);
			log_assert(root && index.editable(root));
			branches = PmuxChoice(index, root).all_arms();
		}
		std::array<std::map<IdString, FactorField>, 2> bitwise;
		match_choice_fields(index, branches, [&](int offset, const auto &bits) { match_bitwise_fields(offset, bits, bitwise); });
		rewrites += factor_local_fields(index, root, branches, bitwise, "factor bitwise operations");
	}
	return rewrites;
}

using SelectKey = std::pair<IdString, SigSpec>;

// 按单元类型和选择信号整理可供复用的输出列。
dict<SelectKey, ChoiceColumns> reusable_columns(PmuxCoarseIndex &index, const std::vector<IdString> &choices)
{
	dict<SelectKey, std::vector<Cell *>> groups;
	for (auto name : choices) {
		auto cell = index.module->cell(name);
		if (index.editable(cell))
			groups[{cell->type, index.port(cell, ID::S)}];
	}
	if (groups.empty())
		return {};
	for (auto cell : index.module->cells()) {
		if (!pmux_has_selection_port(cell, ID::S) || cell->getPort(ID::S).empty())
			continue;
		auto group = groups.find({cell->type, index.port(cell, ID::S)});
		if (group != groups.end())
			group->second.push_back(cell);
	}

	dict<SelectKey, ChoiceColumns> available;
	for (auto &[key, members] : groups) {
		if (GetSize(members) < 2)
			continue;
		std::sort(members.begin(), members.end(), RTLIL::sort_by_name_id<Cell>());
		auto &columns = available[key];
		for (auto cell : members) {
			auto branches = PmuxChoice(index, cell).all_arms();
			auto output = index.port(cell, ID::Y);
			columns.by_branch.resize(branches.size());
			for (int offset = 0; offset < GetSize(output); ++offset) {
				auto source = index.source(output[offset]);
				if (!source || source->cell != cell || source->port != ID::Y || source->offset != offset)
					continue;
				int column = GetSize(columns.columns);
				SigSpec values;
				for (int branch = 0; branch < GetSize(branches); ++branch) {
					auto bit = branches[branch][offset];
					values.append(bit);
					columns.by_branch[branch][bit].push_back(column);
				}
				columns.exact[values].push_back(column);
				if (cell->type == ID($pmux))
					columns.without_default[values.extract(1, GetSize(values) - 1)].push_back(column);
				columns.columns.push_back({std::move(values), output[offset]});
			}
		}
	}
	return available;
}

// 一个选择器可参与联合提取的各类字段。
struct Candidate {
	IdString root;
	std::vector<SigSpec> branches;
	std::vector<FactorField> reused_operands, local_fields, single_operand;
};
// 查找已有选择结果可以复用的字段，并记录其前驱单元。
template <typename Matches> void collect_disjoint_fields(Matches &matches, pool<int> &occupied, std::vector<FactorField> &destination)
{
	for (auto &[key, field] : matches) {
		if (field.offsets.empty() ||
		    std::any_of(field.offsets.begin(), field.offsets.end(), [&](int offset) { return occupied.count(offset); }))
			continue;
		occupied.insert(field.offsets.begin(), field.offsets.end());
		destination.push_back(std::move(field));
	}
}

// 在同一选择条件下收集可提取字段。
std::vector<Candidate> collect_joint_candidates(PmuxCoarseIndex &index, const std::vector<IdString> &choices)
{
	auto available = reusable_columns(index, choices);
	std::vector<Candidate> candidates;
	for (auto name : choices) {
		auto root = index.module->cell(name);
		if (!index.editable(root))
			continue;
		auto columns = available.find({root->type, index.port(root, ID::S)});
		Candidate candidate{name, PmuxChoice(index, root).all_arms(), {}, {}, {}};
		std::map<std::vector<SigBit>, FactorField> nested;
		std::array<std::map<IdString, FactorField>, 2> bitwise;
		std::map<IdString, FactorField> reusable, single_operand;
		auto output = index.port(root, ID::Y);
		pool<SigBit> outputs(output.begin(), output.end());
		match_choice_fields(index, candidate.branches, [&](int offset, const auto &bits) {
			if (columns != available.end())
				match_reusable_field(index, root, outputs, offset, bits, columns->second, reusable, single_operand);
			match_nested_fields(offset, bits, nested);
			match_bitwise_fields(offset, bits, bitwise);
		});
		pool<int> occupied;
		auto collect = [&](auto &matches, auto &destination) { collect_disjoint_fields(matches, occupied, destination); };
		collect(reusable, candidate.reused_operands);
		collect(nested, candidate.local_fields);
		for (auto &group : bitwise)
			collect(group, candidate.local_fields);
		for (auto &[type, field] : single_operand)
			candidate.single_operand.push_back(std::move(field));
		if (candidate.reused_operands.empty() && candidate.local_fields.empty() && candidate.single_operand.empty())
			continue;
		candidates.push_back(std::move(candidate));
	}
	return candidates;
}

// 共用前驱运算的候选单元需要一起计算提取收益。
std::vector<std::vector<int>> group_connected_candidates(const std::vector<Candidate> &candidates)
{
	dict<IdString, int> first_reader;
	mfp<int> connected;
	for (int member = 0; member < GetSize(candidates); ++member) {
		const auto &candidate = candidates[member];
		connected.merge(member, first_reader.emplace(candidate.root, member).first->second);
		for (auto group : {&candidate.reused_operands, &candidate.local_fields, &candidate.single_operand})
			for (const auto &field : *group)
				for (auto producer : field.producers)
					connected.merge(member, first_reader.emplace(producer, member).first->second);
	}
	dict<int, int> group_slots;
	std::vector<std::vector<int>> groups;
	for (int i = 0; i < GetSize(candidates); ++i) {
		auto [slot, inserted] = group_slots.emplace(connected.find(i), GetSize(groups));
		if (inserted)
			groups.emplace_back();
		groups[slot->second].push_back(i);
	}
	return groups;
}

enum class Fields { All, AllWithSingleOperand, ReusedOnly, ReusedWithSingleOperand };

// 按字段优先顺序收集互不重叠的输出位。
ChoiceRewrite make_edit(PmuxCoarseIndex &index, const Candidate &candidate, Fields fields)
{
	ChoiceRewrite edit{index.module->cell(candidate.root), candidate.branches, {}};
	if (!edit.root)
		return edit;
	pool<int> occupied;
	if (fields == Fields::AllWithSingleOperand || fields == Fields::ReusedWithSingleOperand)
		for (const auto &field : candidate.single_operand) {
			edit.fields.push_back(field);
			occupied.insert(field.offsets.begin(), field.offsets.end());
		}
	auto get_field = [](const auto &field) -> const auto & { return field; };
	select_fields(candidate.reused_operands, get_field, occupied, edit.fields);
	if (fields == Fields::All || fields == Fields::AllWithSingleOperand)
		select_fields(candidate.local_fields, get_field, occupied, edit.fields);
	return edit;
}

// 组合一组不重叠的提取字段，检查联合改写收益。
bool apply_group_fields(PmuxCoarseIndex &index, const std::vector<Candidate> &candidates, const std::vector<int> &group, Fields fields)
{
	std::vector<ChoiceRewrite> edits;
	for (int member : group) {
		auto edit = make_edit(index, candidates[member], fields);
		if (!edit.fields.empty())
			edits.push_back(std::move(edit));
	}
	return GetSize(edits) > 1 && apply_factor(index, edits, "factor joint choices", true);
}

// 先尝试联合提取。同组无法共同改写时，依次检查单个选择器。
int apply_joint_group(PmuxCoarseIndex &index, const std::vector<Candidate> &candidates, const std::vector<int> &group)
{
	int rewrites = 0;
	auto apply_group = [&](Fields fields) { return apply_group_fields(index, candidates, group, fields); };
	bool has_single_operand = std::any_of(group.begin(), group.end(), [&](int member) { return !candidates[member].single_operand.empty(); });
	if ((has_single_operand && apply_group(Fields::AllWithSingleOperand)) || apply_group(Fields::All)) {
		return 1;
	}
	for (int member : group) {
		const auto &candidate = candidates[member];
		auto edit = make_edit(index, candidate, Fields::ReusedWithSingleOperand);
		if (edit.fields.empty())
			continue;
		if (apply_factor(index, {edit}, "factor joint choices", true)) {
			++rewrites;
			continue;
		}
		if (!candidate.single_operand.empty() && !candidate.reused_operands.empty())
			rewrites += apply_factor(index, {make_edit(index, candidate, Fields::ReusedOnly)}, "factor joint choices", true);
	}
	return rewrites;
}

// 对有共同前驱的选择器尝试联合提取。
int factor_joint_choices(PmuxCoarseIndex &index)
{
	auto choices = selected_choices(index.module);
	if (choices.empty())
		return 0;
	auto candidates = collect_joint_candidates(index, choices);
	int rewrites = 0;
	for (const auto &group : group_connected_candidates(candidates))
		rewrites += apply_joint_group(index, candidates, group);
	return rewrites;
}

using Reduction = std::pair<IdString, SigSpec>;
using ReductionResults = std::map<Reduction, std::vector<IdString>>;

// 将归约输入整理为可比较的运算及数据。
std::optional<Reduction> normalize_reduction(IdString type, const SigSpec &input)
{
	if (type == ID($reduce_bool))
		type = ID($reduce_or);
	bool parity = type.in(ID($reduce_xor), ID($reduce_xnor));
	bool and_gate = type == ID($reduce_and);
	bool invert = type == ID($reduce_xnor);
	std::set<SigBit> remaining;
	for (SigBit bit : input) {
		if (bit.wire) {
			auto [it, inserted] = remaining.insert(bit);
			if (parity && !inserted)
				remaining.erase(it);
			continue;
		}
		if (bit != State::S0 && bit != State::S1)
			return std::nullopt;
		if (!parity && (bit == State::S1) != and_gate)
			return Reduction{IdString(), bit};
		invert ^= parity && bit == State::S1;
	}
	if (remaining.empty())
		return Reduction{IdString(), SigSpec(and_gate || invert ? State::S1 : State::S0)};
	SigSpec operands;
	for (SigBit bit : remaining)
		operands.append(bit);
	if (GetSize(operands) == 1)
		return Reduction{invert ? ID($not) : IdString(), operands};
	if (parity)
		type = invert ? ID($reduce_xnor) : ID($reduce_xor);
	return Reduction{type, operands};
}

// 登记可供后续分支复用的归约结果。
void record_reduction(PmuxCoarseIndex &index, Cell *cell, ReductionResults &available)
{
	if (GetSize(cell->getPort(ID::Y)) != 1)
		return;
	auto input = index.port(cell, ID::A);
	if (cell->type == ID($not) && GetSize(input) != 1)
		return;
	auto value = cell->type == ID($not) ? std::optional<Reduction>{{cell->type, input}} : normalize_reduction(cell->type, input);
	if (!value || value->first.empty())
		return;
	if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
		// 被抵消的重复位在原单元中仍可能传播未定义值。
		if (std::count_if(input.begin(), input.end(), [](SigBit bit) { return bit.wire; }) != GetSize(value->second))
			return;
	}
	available[*value].push_back(cell->name);
}

// 复用已有归约单元，为其余分支生成归约结果。
std::vector<IdString> emit_reductions(PmuxCoarseIndex &index, Cell *root, ReductionResults &available, std::map<Reduction, SigSpec> &results,
				      PmuxRewrite &candidate)
{
	pool<SigBit> outputs{index.port(root, ID::Y).as_bit()};
	std::vector<IdString> added;
	for (auto &[value, result] : results) {
		const auto &[type, input] = value;
		if (type.empty()) {
			result = input;
			continue;
		}
		auto found = available.find(value);
		if (found != available.end())
			for (auto name : found->second) {
				auto cell = index.module->cell(name);
				if (!cell || cell == root)
					continue;
				auto bit = index.port(cell, ID::Y).as_bit();
				if (index.driver(bit) == cell && index.independent({bit}, outputs)) {
					result = bit;
					break;
				}
			}
		if (!result.empty())
			continue;
		auto &staging = candidate.staging;
		result = staging.addWire(NEW_ID);
		auto cell = pmux_emit_reduce(&staging, type, input, result, root->get_src_attribute());
		added.push_back(cell->name);
	}
	return added;
}

// 将选择之后的归约分配到分支并复用已有结果。
bool factor_reduction(PmuxCoarseIndex &index, Cell *root, ReductionResults &available)
{
	if (!index.editable(root) || GetSize(index.port(root, ID::Y)) != 1)
		return false;
	auto input = index.port(root, ID::A);
	auto mux = input.empty() ? nullptr : index.driver(input[0]);
	if (!mux || !pmux_has_selection_port(mux, ID::S) || mux->getPort(ID::S).empty())
		return false;
	std::vector<int> offsets;
	for (auto bit : input) {
		auto source = index.source(bit);
		if (!source || source->cell != mux || source->port != ID::Y)
			return false;
		offsets.push_back(source->offset);
	}
	std::map<Reduction, SigSpec> results;
	std::vector<Reduction> values;
	for (const auto &arm : PmuxChoice(index, mux).all_arms()) {
		SigSpec branch;
		for (int offset : offsets)
			branch.append(arm[offset]);
		if (branch.is_fully_const() && branch.as_const().is_fully_undef_x_only()) {
			values.emplace_back(IdString(), State::Sx);
			continue;
		}
		auto value = normalize_reduction(root->type, branch);
		if (!value)
			return false;
		values.push_back(*value);
		results.try_emplace(*value);
	}
	if (results.empty())
		return false;

	PmuxRewrite candidate(index.module, index, "factor reduction");
	auto added = emit_reductions(index, root, available, results, candidate);
	std::vector<SigSpec> branches;
	for (const auto &value : values)
		branches.push_back(value.first.empty() ? value.second : results.at(value));
	candidate.connect(root->getPort(ID::Y), pmux_build_choice(&candidate.staging, index.port(mux, ID::S), branches));
	candidate.find_removable({root, mux});
	if (!candidate.removed.count(root) || (candidate.added_count() && !candidate.removed.count(mux)) || !candidate.validate())
		return false;
	candidate.commit();
	for (auto name : added)
		record_reduction(index, index.module->cell(name), available);
	return true;
}

// 在模块内查找可以共同使用的归约表达式。
int factor_reductions(PmuxCoarseIndex &index)
{
	std::vector<IdString> reductions;
	ReductionResults available;
	for (auto cell : index.module->cells()) {
		bool reduction = cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
		if (reduction && index.module->design->selected(index.module, cell))
			reductions.push_back(cell->name);
		if (reduction || cell->type == ID($not))
			record_reduction(index, cell, available);
	}
	std::sort(reductions.begin(), reductions.end());
	for (auto &[value, names] : available)
		std::sort(names.begin(), names.end());

	int rewrites = 0;
	for (auto name : reductions) {
		auto cell = index.module->cell(name);
		if (cell)
			rewrites += factor_reduction(index, cell, available);
	}
	return rewrites;
}

// 注册选择分支公共运算提取 Pass。
struct OptPmuxFactorPass : public Pass {
	// 注册 opt_pmux_factor 命令。
	OptPmuxFactorPass() : Pass("opt_pmux_factor", "factor common operations around selections") {}

	// 说明局部提取、联合提取和归约共享。
	void help() override
	{
		log("\n");
		log("    opt_pmux_factor [selection]\n");
		log("\n");
		log("Factor common bitwise operations or nested muxes across output fields,\n");
		log("reuse either or both operand selections and factor shared producers together,\n");
		log("and move reductions to their input branches when the selection can be\n");
		log("removed or all defined branches share one reusable reduction result.\n");
		log("\n");
	}

	// 在同一模块索引上依次执行三项公共运算提取。
	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		pmux_run_pass(design, "opt_pmux_factor", "Executing OPT_PMUX_FACTOR pass.\n", [](Module *module) {
			PmuxCoarseIndex index(module);
			int rewrites = factor_local_choices(index);
			rewrites += factor_joint_choices(index);
			return rewrites + factor_reductions(index);
		});
	}
} OptPmuxFactorPass;

PRIVATE_NAMESPACE_END

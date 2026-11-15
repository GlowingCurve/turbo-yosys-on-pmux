#include "kernel/log.h"
#include "kernel/register.h"
#include "pmux_common.h"
#include "pmux_rewrite.h"

#include <algorithm>
#include <array>
#include <map>
#include <optional>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

std::vector<SigSpec> choice_branches(PmuxCoarseIndex &index, Cell *cell)
{
	auto a = index.port(cell, ID::A), b = index.port(cell, ID::B);
	int width = GetSize(cell->getPort(ID::Y)), selects = GetSize(cell->getPort(ID::S));
	log_assert(cell->type == ID($pmux) || (cell->type == ID($mux) && selects == 1));
	log_assert(GetSize(a) == width && GetSize(b) == width * selects);
	std::vector<SigSpec> branches{a};
	for (int i = 0; i < selects; ++i)
		branches.push_back(b.extract(i * width, width));
	return branches;
}

// Collapse a choice when its defined branches agree, and report a generated selector by name.
SigSpec build_choice(Module *module, const SigSpec &select, const std::vector<SigSpec> &values,
		IdString type = ID($mux), IdString *created = nullptr)
{
	const SigSpec *common = nullptr;
	for (const auto &value : values) {
		if (value.is_fully_const() && value.as_const().is_fully_undef_x_only())
			continue;
		if (common && *common != value) {
			SigSpec cases;
			for (int i = 1; i < GetSize(values); ++i)
				cases.append(values[i]);
			auto name = NEW_ID;
			if (created)
				*created = name;
			return type == ID($mux) && GetSize(select) == 1 ? module->Mux(name, values.front(), cases, select)
					: module->Pmux(name, values.front(), cases, select);
		}
		common = &value;
	}
	return common ? *common : values.front();
}

struct FactorBit
{
	SigBit value;
	Cell *producer = nullptr;
	SigBit a, b, select;
};

struct FactorField
{
	enum class Input { FixedOperands, SelectedOperand, SelectedControl };
	Input input = Input::FixedOperands;
	IdString type;
	std::vector<int> offsets;
	SigSpec a, b;
	std::vector<SigSpec> branches;
	pool<IdString> producers;

	void append(int offset, SigBit left, const pool<IdString> &cells)
	{
		offsets.push_back(offset);
		a.append(left);
		producers.insert(cells.begin(), cells.end());
	}

	SigSpec emit(Module *module, const SigSpec &select) const
	{
		auto operand = input == Input::FixedOperands ? b : build_choice(module, select, branches);
		if (input == Input::SelectedControl)
			return module->Mux(NEW_ID, a, b, operand);
		return pmux_emit_bitwise_choice(module, type, a, operand);
	}
};

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
		auto a0 = value(inputs[0]), b0 = value(inputs[1]), a1 = value(inputs[2]), b1 = value(inputs[3]);
		auto first = pmux_eval_bitwise(type, a0, b0);
		if (first != State::Sx && first == pmux_eval_bitwise(type, a1, b1) &&
				first != pmux_eval_bitwise(type, a0 == a1 ? a0 : State::Sx, b0 == b1 ? b0 : State::Sx))
			return false;
	}
	return true;
}

struct ChoiceColumns
{
	struct Column { SigSpec values; SigBit output; };
	std::vector<Column> columns;
	std::vector<dict<SigBit, std::vector<int>>> by_branch;
	dict<SigSpec, std::vector<int>> exact, without_default;
};

void match_reusable_field(PmuxCoarseIndex &index, Cell *root, const pool<SigBit> &outputs, int offset,
		const std::vector<FactorBit> &bits, const ChoiceColumns &available, std::map<IdString, FactorField> &reused,
		std::map<IdString, FactorField> &single_operand)
{
	bool ignore_default = root->type == ID($pmux) && bits.front().value == State::Sx;
	int first = ignore_default ? 1 : 0;
	if (!bits[first].producer || bits[first].producer->type == ID($mux))
		return;
	IdString type = bits[first].producer->type;
	std::array<const std::vector<int> *, 2> candidates{};
	int fewest = GetSize(available.columns) + 1;
	pool<IdString> producers;
	for (int branch = first; branch < GetSize(bits); ++branch) {
		const auto &bit = bits[branch];
		if (!bit.producer || bit.producer->type != type)
			return;
		producers.insert(bit.producer->name);
		const auto &row = available.by_branch[branch];
		auto left = row.find(bit.a), right = row.find(bit.b);
		int size = (left == row.end() ? 0 : GetSize(left->second)) +
				(right == row.end() || bit.a == bit.b ? 0 : GetSize(right->second));
		if (size < fewest) {
			fewest = size;
			candidates = {left == row.end() ? nullptr : &left->second,
					right == row.end() || bit.a == bit.b ? nullptr : &right->second};
		}
	}

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
			SigSpec values;
			for (int branch = first; branch < GetSize(bits); ++branch) {
				const auto &bit = bits[branch];
				if (left.values[branch] != bit.a && left.values[branch] != bit.b)
					break;
				values.append(left.values[branch] == bit.a ? bit.b : bit.a);
			}
			if (GetSize(values) != GetSize(bits) - first)
				continue;
			if (root->type == ID($mux) && !preserves_unknown_select(type, left.values, values))
				continue;
			if (auto matching = lookup.find(values); matching != lookup.end()) {
				for (int other : matching->second) {
					SigBit right = available.columns[other].output;
					if (outputs.count(right) || !index.independent({left.output, right}, outputs))
						continue;
					auto &field = reused[type];
					field.type = type;
					field.append(offset, left.output, producers);
					field.b.append(right);
					return;
				}
			}
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
	if (!existing_operand.wire)
		return;
	auto &field = single_operand[type];
	field.input = FactorField::Input::SelectedOperand;
	field.type = type;
	field.append(offset, existing_operand, producers);
	field.branches.resize(bits.size());
	for (int branch = 0; branch < GetSize(bits); ++branch)
		field.branches[branch].append(branch < first ? SigBit(State::Sx) : missing_operand[branch - first]);
}

void match_nested_fields(int offset, const std::vector<FactorBit> &bits,
		std::map<std::vector<SigBit>, FactorField> &fields)
{
	for (const auto &seed : bits) {
		if (!seed.producer || seed.producer->type != ID($mux))
			continue;
		std::vector<SigBit> conditions;
		pool<IdString> producers;
		for (const auto &branch : bits) {
			if (branch.value == State::Sx || branch.value == seed.a || branch.value == seed.b) {
				conditions.emplace_back(branch.value == State::Sx ? State::Sx : branch.value == seed.a ? State::S0 : State::S1);
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

void match_bitwise_fields(int offset, const std::vector<FactorBit> &bits,
		std::array<std::map<IdString, FactorField>, 2> &fields)
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

template <typename Match>
void match_choice_fields(PmuxCoarseIndex &index, const std::vector<SigSpec> &branches, Match match)
{
	struct Inputs { SigSpec a, b; SigBit select; };
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
					bool sign = pmux_is_signed_port(cell, ID::A) && pmux_is_signed_port(cell, ID::B);
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

struct ChoiceRewrite
{
	Cell *root;
	const std::vector<SigSpec> *branches;
	std::vector<const FactorField *> fields;
};

// Keep fields in preference order and omit fields that overlap one already chosen.
template<typename Range, typename Field>
void select_fields(const Range &range, Field field_of, pool<int> &occupied, std::vector<const FactorField *> &selected)
{
	for (const auto &entry : range) {
		const auto &field = field_of(entry);
		if (field.offsets.empty() || std::any_of(field.offsets.begin(), field.offsets.end(), [&](int offset) { return occupied.count(offset); }))
			continue;
		occupied.insert(field.offsets.begin(), field.offsets.end());
		selected.push_back(&field);
	}
}

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
		for (const auto *field : fields) {
			for (auto name : field->producers)
				if (auto cell = index.module->cell(name))
					region.insert(cell);
			SigSpec field_output;
			for (int offset : field->offsets) {
				log_assert(factored.insert(offset).second);
				field_output.append(output[offset]);
			}
			rewrite.connect(field_output, field->emit(&rewrite.staging, select));
		}
		SigSpec remaining_output;
		std::vector<SigSpec> remaining_branches(branches->size());
		for (int offset = 0; offset < GetSize(output); ++offset) {
			if (factored.count(offset))
				continue;
			remaining_output.append(output[offset]);
			for (int branch = 0; branch < GetSize(remaining_branches); ++branch)
				remaining_branches[branch].append((*branches)[branch][offset]);
		}
		if (!remaining_output.empty())
			rewrite.connect(remaining_output, build_choice(&rewrite.staging, select, remaining_branches, root->type, &residual));
	}
	rewrite.find_removable(region);
	if (require_reduction && GetSize(rewrite.removed) <= rewrite.added_count())
		return false;
	for (const auto &edit : edits)
		for (const auto *field : edit.fields)
			if (std::none_of(field->producers.begin(), field->producers.end(),
					[&](IdString name) { return rewrite.removed.count(index.module->cell(name)); }))
				return false;
	if (!rewrite.validate())
		return false;
	rewrite.commit();
	if (remaining_choice)
		*remaining_choice = residual;
	return true;
}

template<typename Maps>
bool factor_local_fields(PmuxCoarseIndex &index, Cell *root, const std::vector<SigSpec> &branches, const Maps &matches,
		const char *rule, IdString *remaining_choice = nullptr)
{
	auto apply = [&](const std::vector<const FactorField *> &fields) {
		return apply_factor(index, {{root, &branches, fields}}, rule, false, remaining_choice);
	};
	std::vector<const FactorField *> single_fields;
	for (const auto &variant : matches) {
		std::vector<const FactorField *> fields;
		pool<int> occupied;
		select_fields(variant, [](const auto &entry) -> const auto & { return entry.second; }, occupied, fields);
		for (const auto &[type, field] : variant)
			if (!field.offsets.empty())
				single_fields.push_back(&field);
		if (GetSize(fields) > 1 && apply(fields))
			return true;
	}
	for (const auto *field : single_fields)
		if (apply({field}))
			return true;
	return false;
}

std::vector<IdString> selected_choices(Module *module)
{
	std::vector<IdString> choices;
	for (auto cell : module->selected_cells())
		if (pmux_has_selection_port(cell, ID::S) && !cell->getPort(ID::S).empty())
			choices.push_back(cell->name);
	std::sort(choices.begin(), choices.end());
	return choices;
}

int factor_local_choices(PmuxCoarseIndex &index)
{
	int rewrites = 0;
	for (auto name : selected_choices(index.module)) {
		auto root = index.module->cell(name);
		if (!root || !index.editable(root))
			continue;
		auto branches = choice_branches(index, root);
		std::array<std::map<std::vector<SigBit>, FactorField>, 1> nested;
		match_choice_fields(index, branches, [&](int offset, const auto &bits) { match_nested_fields(offset, bits, nested.front()); });
		IdString remaining_choice;
		if (factor_local_fields(index, root, branches, nested, "factor nested selections", &remaining_choice)) {
			++rewrites;
			if (remaining_choice.empty())
				continue;
			root = index.module->cell(remaining_choice);
			log_assert(root && index.editable(root));
			branches = choice_branches(index, root);
		}
		std::array<std::map<IdString, FactorField>, 2> bitwise;
		match_choice_fields(index, branches, [&](int offset, const auto &bits) { match_bitwise_fields(offset, bits, bitwise); });
		rewrites += factor_local_fields(index, root, branches, bitwise, "factor bitwise operations");
	}
	return rewrites;
}

using SelectKey = std::pair<IdString, SigSpec>;

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
		if (auto group = groups.find({cell->type, index.port(cell, ID::S)}); group != groups.end())
			group->second.push_back(cell);
	}

	dict<SelectKey, ChoiceColumns> available;
	for (auto &[key, members] : groups) {
		if (GetSize(members) < 2)
			continue;
		std::sort(members.begin(), members.end(), RTLIL::sort_by_name_id<Cell>());
		auto &columns = available[key];
		for (auto cell : members) {
			auto branches = choice_branches(index, cell);
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

int factor_joint_choices(PmuxCoarseIndex &index)
{
	auto choices = selected_choices(index.module);
	if (choices.empty())
		return 0;
	auto available = reusable_columns(index, choices);

	struct Candidate {
		IdString root;
		std::vector<SigSpec> branches;
		std::vector<FactorField> reused_operands, local_fields, single_operand;
	};
	std::vector<Candidate> candidates;
	dict<IdString, int> first_reader;
	mfp<int> connected;
	for (auto name : choices) {
		auto root = index.module->cell(name);
		if (!index.editable(root))
			continue;
		auto columns = available.find({root->type, index.port(root, ID::S)});
		Candidate candidate{name, choice_branches(index, root), {}, {}, {}};
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
		auto collect = [&](auto &matches, auto &destination) {
			for (auto &[key, field] : matches) {
				if (field.offsets.empty() || std::any_of(field.offsets.begin(), field.offsets.end(), [&](int offset) { return occupied.count(offset); }))
					continue;
				occupied.insert(field.offsets.begin(), field.offsets.end());
				destination.push_back(std::move(field));
			}
		};
		collect(reusable, candidate.reused_operands);
		collect(nested, candidate.local_fields);
		for (auto &group : bitwise)
			collect(group, candidate.local_fields);
		for (auto &[type, field] : single_operand)
			candidate.single_operand.push_back(std::move(field));
		if (candidate.reused_operands.empty() && candidate.local_fields.empty() && candidate.single_operand.empty())
			continue;
		int member = GetSize(candidates);
		connected.merge(member, first_reader.emplace(name, member).first->second);
		for (auto group : {&candidate.reused_operands, &candidate.local_fields, &candidate.single_operand})
			for (const auto &field : *group)
				for (auto producer : field.producers)
					connected.merge(member, first_reader.emplace(producer, member).first->second);
		candidates.push_back(std::move(candidate));
	}

	enum class Fields { All, AllWithSingleOperand, ReusedOnly, ReusedWithSingleOperand };
	auto make_edit = [&](const Candidate &candidate, Fields fields) {
		ChoiceRewrite edit{index.module->cell(candidate.root), &candidate.branches, {}};
		if (!edit.root)
			return edit;
		pool<int> occupied;
		if (fields == Fields::AllWithSingleOperand || fields == Fields::ReusedWithSingleOperand)
			for (const auto &field : candidate.single_operand) {
				edit.fields.push_back(&field);
				occupied.insert(field.offsets.begin(), field.offsets.end());
			}
		auto get_field = [](const auto &field) -> const auto & { return field; };
		select_fields(candidate.reused_operands, get_field, occupied, edit.fields);
		if (fields == Fields::All || fields == Fields::AllWithSingleOperand)
			select_fields(candidate.local_fields, get_field, occupied, edit.fields);
		return edit;
	};
	dict<int, int> group_slots;
	std::vector<std::vector<int>> groups;
	for (int i = 0; i < GetSize(candidates); ++i) {
		auto [slot, inserted] = group_slots.emplace(connected.find(i), GetSize(groups));
		if (inserted)
			groups.emplace_back();
		groups[slot->second].push_back(i);
	}
	int rewrites = 0;
	for (const auto &group : groups) {
		auto apply_group = [&](Fields fields) {
			std::vector<ChoiceRewrite> edits;
			for (int member : group) {
				auto edit = make_edit(candidates[member], fields);
				if (!edit.fields.empty())
					edits.push_back(std::move(edit));
			}
			return GetSize(edits) > 1 && apply_factor(index, edits, "factor joint choices", true);
		};
		bool has_single_operand = std::any_of(group.begin(), group.end(), [&](int member) {
			return !candidates[member].single_operand.empty();
		});
		if ((has_single_operand && apply_group(Fields::AllWithSingleOperand)) || apply_group(Fields::All)) {
			++rewrites;
			continue;
		}
		for (int member : group) {
			const auto &candidate = candidates[member];
			auto edit = make_edit(candidate, Fields::ReusedWithSingleOperand);
			if (edit.fields.empty())
				continue;
			if (apply_factor(index, {edit}, "factor joint choices", true)) {
				++rewrites;
				continue;
			}
			if (!candidate.single_operand.empty() && !candidate.reused_operands.empty())
				rewrites += apply_factor(index, {make_edit(candidate, Fields::ReusedOnly)}, "factor joint choices", true);
		}
	}
	return rewrites;
}

using Reduction = std::pair<IdString, SigSpec>;
using ReductionResults = std::map<Reduction, std::vector<IdString>>;

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
	for (const auto &arm : choice_branches(index, mux)) {
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
	pool<SigBit> outputs{index.port(root, ID::Y).as_bit()};
	std::vector<IdString> added;
	for (auto &[value, result] : results) {
		const auto &[type, input] = value;
		if (type.empty()) {
			result = input;
			continue;
		}
		if (auto found = available.find(value); found != available.end())
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
		auto name = NEW_ID;
		auto src = root->get_src_attribute();
		if (type == ID($not))
			staging.addNot(name, input, result, false, src);
		else if (type == ID($reduce_and))
			staging.addReduceAnd(name, input, result, false, src);
		else if (type == ID($reduce_or))
			staging.addReduceOr(name, input, result, false, src);
		else if (type == ID($reduce_xor))
			staging.addReduceXor(name, input, result, false, src);
		else {
			log_assert(type == ID($reduce_xnor));
			staging.addReduceXnor(name, input, result, false, src);
		}
		added.push_back(name);
	}
	std::vector<SigSpec> branches;
	for (const auto &value : values)
		branches.push_back(value.first.empty() ? value.second : results.at(value));
	candidate.connect(root->getPort(ID::Y), build_choice(&candidate.staging, index.port(mux, ID::S), branches));
	candidate.find_removable({root, mux});
	if (!candidate.removed.count(root) || (candidate.added_count() && !candidate.removed.count(mux)) || !candidate.validate())
		return false;
	candidate.commit();
	for (auto name : added)
		record_reduction(index, index.module->cell(name), available);
	return true;
}

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
	for (auto name : reductions)
		if (auto cell = index.module->cell(name))
			rewrites += factor_reduction(index, cell, available);
	return rewrites;
}

struct OptPmuxFactorPass : public Pass
{
	OptPmuxFactorPass() : Pass("opt_pmux_factor", "factor common operations around selections") {}

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

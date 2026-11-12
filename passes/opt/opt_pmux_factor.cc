#include "kernel/log.h"
#include "kernel/register.h"
#include "pmux_rewrite.h"

#include <algorithm>
#include <array>
#include <map>
#include <optional>
#include <set>
#include <tuple>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool unspecified(const SigSpec &value)
{
	return value.is_fully_const() && value.as_const().is_fully_undef_x_only();
}

struct FactorChoice
{
	SigSpec select;
	std::vector<SigSpec> branches;

	static std::optional<FactorChoice> read(PmuxCoarseIndex &index, Cell *cell)
	{
		if (!cell->type.in(ID($mux), ID($pmux)))
			return std::nullopt;
		SigSpec select = index.port(cell, ID::S);
		SigSpec a = index.port(cell, ID::A);
		SigSpec b = index.port(cell, ID::B);
		int width = GetSize(index.port(cell, ID::Y));
		if (select.empty() || (cell->type == ID($mux) && GetSize(select) != 1) ||
				GetSize(a) != width || GetSize(b) != width * GetSize(select))
			return std::nullopt;
		FactorChoice choice{select, {a}};
		for (int i = 0; i < GetSize(select); i++)
			choice.branches.push_back(b.extract(i * width, width));
		return choice;
	}
};

// Use the defined value directly when every defined branch agrees.
std::optional<SigSpec> common_value(const std::vector<SigSpec> &values)
{
	SigSpec common;
	for (const auto &value : values) {
		if (unspecified(value))
			continue;
		if (!common.empty() && common != value)
			return std::nullopt;
		common = value;
	}
	return common.empty() ? values.front() : common;
}

SigSpec emit_choice(Module *module, const SigSpec &select, const std::vector<SigSpec> &values, IdString type = ID($mux))
{
	if (auto common = common_value(values))
		return *common;
	SigSpec cases;
	for (int i = 1; i < GetSize(values); i++)
		cases.append(values[i]);
	return type == ID($mux) && GetSize(select) == 1 ? module->Mux(NEW_ID, values.front(), cases, select)
		: module->Pmux(NEW_ID, values.front(), cases, select);
}

std::optional<std::pair<Cell *, FactorChoice>> choice_input(PmuxCoarseIndex &index, const SigSpec &value)
{
	if (value.empty())
		return std::nullopt;
	Cell *cell = index.driver(value[0]);
	if (!cell)
		return std::nullopt;
	auto choice = FactorChoice::read(index, cell);
	if (!choice)
		return std::nullopt;

	std::vector<int> offsets;
	for (auto bit : value) {
		auto source = index.source(bit);
		if (!source || source->cell != cell || source->port != ID::Y)
			return std::nullopt;
		offsets.push_back(source->offset);
	}
	if (index.port(cell, ID::Y) != value) {
		for (auto &branch : choice->branches) {
			SigSpec field;
			for (int offset : offsets)
				field.append(branch[offset]);
			branch = std::move(field);
		}
	}
	return std::make_pair(cell, std::move(*choice));
}

bool prepare_factor(PmuxCoarseIndex &index, const pool<Cell *> &roots, const pool<Cell *> &region, PmuxRewrite &rewrite)
{
	pool<SigBit> input_bits, output_bits;
	for (auto root : roots)
		for (auto bit : index.port(root, ID::Y))
			output_bits.insert(bit);
	auto retain = [&](const SigSpec &input) {
		for (auto bit : input)
			if (bit.wire && bit.wire->module == index.module && !output_bits.count(index.sigmap(bit)))
				input_bits.insert(bit);
	};
	for (Cell *cell : rewrite.staging.cells())
		for (const auto &[port, signal] : cell->connections())
			if (cell->input(port))
				retain(signal);
	for (const auto &connection : rewrite.staging.connections())
		retain(connection.second);
	rewrite.removed = index.removable(region, {}, output_bits, input_bits);
	return std::all_of(roots.begin(), roots.end(), [&](auto root) { return rewrite.removed.count(root); });
}

bool bitwise_type(IdString type)
{
	return type.in(ID($and), ID($or), ID($xor), ID($xnor));
}

struct FactorDriver
{
	SigSpec a, b;
	SigBit select;

	static FactorDriver read(PmuxCoarseIndex &index, Cell *cell)
	{
		auto a = index.port(cell, ID::A);
		auto b = index.port(cell, ID::B);
		if (cell->type == ID($mux))
			return {a, b, index.port(cell, ID::S).as_bit()};
		bool is_signed = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
		int width = GetSize(cell->getPort(ID::Y));
		a.extend_u0(width, is_signed);
		b.extend_u0(width, is_signed);
		return {a, b, {}};
	}
};

struct FactorBit
{
	SigBit value;
	Cell *producer;
	SigBit a, b, select;

	static FactorBit read(PmuxCoarseIndex &index, dict<Cell *, FactorDriver> &drivers, SigBit bit)
	{
		auto source = index.source(bit);
		if (!source || source->port != ID::Y ||
				(source->cell->type != ID($mux) && !bitwise_type(source->cell->type)))
			return {bit, nullptr, {}, {}, {}};
		Cell *cell = source->cell;
		auto entry = drivers.find(cell);
		if (entry == drivers.end())
			entry = drivers.emplace(cell, FactorDriver::read(index, cell)).first;
		const auto &driver = entry->second;
		return {bit, cell, driver.a[source->offset], driver.b[source->offset], driver.select};
	}
};

struct FactorField
{
	IdString type;
	std::vector<int> offsets;
	SigSpec a, b;
	std::vector<SigSpec> branches;
	pool<Cell *> producers;

	bool operator==(const FactorField &other) const
	{
		return std::tie(type, offsets, a, b, branches) == std::tie(other.type, other.offsets, other.a, other.b, other.branches);
	}

	SigSpec emit(Module *module, const SigSpec &select) const
	{
		auto input = branches.empty() ? b : emit_choice(module, select, branches);
		if (type == ID($mux))
			return module->Mux(NEW_ID, a, b, input);
		Wire *output = module->addWire(NEW_ID, GetSize(a));
		if (type == ID($and))
			module->addAnd(NEW_ID, a, input, output);
		else if (type == ID($or))
			module->addOr(NEW_ID, a, input, output);
		else if (type == ID($xor))
			module->addXor(NEW_ID, a, input, output);
		else
			module->addXnor(NEW_ID, a, input, output);
		return output;
	}
};

struct ChoiceColumns
{
	struct Column {
		SigSpec values;
		SigBit output;
	};
	std::vector<Column> columns;
	std::vector<dict<SigBit, std::vector<int>>> by_branch;
	dict<SigSpec, std::vector<int>> exact, without_default;
	int cells = 0;

	void add(PmuxCoarseIndex &index, Cell *cell, const FactorChoice &choice)
	{
		++cells;
		by_branch.resize(choice.branches.size());
		auto output = index.port(cell, ID::Y);
		for (int offset = 0; offset < GetSize(output); ++offset) {
			auto source = index.source(output[offset]);
			if (!source || source->cell != cell || source->port != ID::Y || source->offset != offset)
				continue;
			int column = GetSize(columns);
			SigSpec values;
			for (int branch = 0; branch < GetSize(choice.branches); ++branch) {
				auto value = choice.branches[branch][offset];
				values.append(value);
				by_branch[branch][value].push_back(column);
			}
			exact[values].push_back(column);
			if (cell->type == ID($pmux))
				without_default[values.extract(1, GetSize(values) - 1)].push_back(column);
			columns.push_back({std::move(values), output[offset]});
		}
	}
};

State bitwise_value(IdString type, State a, State b)
{
	if (type == ID($and)) {
		if (a == State::S0 || b == State::S0)
			return State::S0;
		return a == State::S1 && b == State::S1 ? State::S1 : State::Sx;
	}
	if (type == ID($or)) {
		if (a == State::S1 || b == State::S1)
			return State::S1;
		return a == State::S0 && b == State::S0 ? State::S0 : State::Sx;
	}
	if (a > State::S1 || b > State::S1)
		return State::Sx;
	return ((a != b) == (type == ID($xor))) ? State::S1 : State::S0;
}

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
			if (!bit.wire)
				return bit.data <= State::S1 ? bit.data : State::Sx;
			return State(code / weights.at(bit) % 3);
		};
		auto a0 = value(inputs[0]), b0 = value(inputs[1]), a1 = value(inputs[2]), b1 = value(inputs[3]);
		auto first = bitwise_value(type, a0, b0);
		if (first <= State::S1 && first == bitwise_value(type, a1, b1) &&
				first != bitwise_value(type, a0 == a1 ? a0 : State::Sx, b0 == b1 ? b0 : State::Sx))
			return false;
	}
	return true;
}

void match_reusable_field(PmuxCoarseIndex &index, Cell *root, const pool<SigBit> &outputs, int offset,
		const std::vector<FactorBit> &bits, const ChoiceColumns &available, std::map<IdString, FactorField> &fields,
		std::map<IdString, FactorField> &single_operand)
{
	bool ignore_default = root->type == ID($pmux) && bits.front().value == State::Sx;
	int first = ignore_default ? 1 : 0;
	if (!bits[first].producer || !bitwise_type(bits[first].producer->type))
		return;
	IdString type = bits[first].producer->type;
	const std::vector<int> *left_candidates = nullptr, *right_candidates = nullptr;
	int fewest = GetSize(available.columns) + 1;
	pool<Cell *> producers;
	for (int branch = first; branch < GetSize(bits); ++branch) {
		const auto &bit = bits[branch];
		if (!bit.producer || bit.producer->type != type)
			return;
		producers.insert(bit.producer);
		const auto &row = available.by_branch[branch];
		auto left = row.find(bit.a), right = row.find(bit.b);
		int size = (left == row.end() ? 0 : GetSize(left->second)) +
				(right == row.end() || bit.a == bit.b ? 0 : GetSize(right->second));
		if (size < fewest) {
			fewest = size;
			left_candidates = left == row.end() ? nullptr : &left->second;
			right_candidates = right == row.end() || bit.a == bit.b ? nullptr : &right->second;
		}
	}

	std::optional<std::pair<SigBit, SigSpec>> missing_selection;
	for (const auto *candidates : {left_candidates, right_candidates}) {
		if (!candidates)
			continue;
		for (int column : *candidates) {
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
			const auto &lookup = ignore_default ? available.without_default : available.exact;
			auto matching = lookup.find(values);
			if (root->type == ID($mux) && !preserves_unknown_select(type, left.values, values))
				continue;
			if (matching != lookup.end()) {
				for (int other : matching->second) {
					SigBit right = available.columns[other].output;
					if (outputs.count(right) || !index.independent({left.output, right}, outputs))
						continue;
					auto &field = fields[type];
					field.type = type;
					field.offsets.push_back(offset);
					field.a.append(left.output);
					field.b.append(right);
					field.producers.insert(producers.begin(), producers.end());
					return;
				}
			}
			if (!missing_selection) {
				pool<SigBit> inputs(values.begin(), values.end());
				inputs.insert(left.output);
				if (index.independent(inputs, outputs))
					missing_selection.emplace(left.output, std::move(values));
			}
		}
	}
	if (!missing_selection)
		return;
	const auto &[existing, values] = *missing_selection;
	auto &field = single_operand[type];
	field.type = type;
	field.offsets.push_back(offset);
	field.a.append(existing);
	field.branches.resize(bits.size());
	if (ignore_default)
		field.branches.front().append(State::Sx);
	for (int branch = first; branch < GetSize(bits); ++branch)
		field.branches[branch].append(values[branch - first]);
	field.producers.insert(producers.begin(), producers.end());
}

void match_nested_fields(int offset, const std::vector<FactorBit> &bits,
		std::map<std::vector<SigBit>, FactorField> &fields)
{
	for (const auto &seed : bits) {
		if (!seed.producer || seed.producer->type != ID($mux))
			continue;
		std::vector<SigBit> conditions;
		pool<Cell *> producers;
		for (const auto &branch : bits) {
			if (branch.value == State::Sx)
				conditions.emplace_back(State::Sx);
			else if (branch.value == seed.a)
				conditions.emplace_back(State::S0);
			else if (branch.value == seed.b)
				conditions.emplace_back(State::S1);
			else if (branch.producer && branch.producer->type == ID($mux) && branch.a == seed.a && branch.b == seed.b) {
				conditions.push_back(branch.select);
				producers.insert(branch.producer);
			} else {
				break;
			}
		}
		if (conditions.size() != bits.size() || producers.empty())
			continue;
		auto &field = fields[conditions];
		if (field.offsets.empty()) {
			field.type = ID($mux);
			for (auto condition : conditions)
				field.branches.emplace_back(condition);
		}
		field.offsets.push_back(offset);
		field.a.append(seed.a);
		field.b.append(seed.b);
		field.producers.insert(producers.begin(), producers.end());
		break;
	}
}

void match_bitwise_field(FactorField &field, int offset, const std::vector<FactorBit> &bits, SigBit common)
{
	std::vector<SigBit> operands;
	pool<Cell *> producers;
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
			return;
		operands.push_back(branch.a == common ? branch.b : branch.a);
		producers.insert(branch.producer);
	}
	if (producers.empty())
		return;
	field.offsets.push_back(offset);
	field.a.append(common);
	field.producers.insert(producers.begin(), producers.end());
	field.branches.resize(operands.size());
	for (int i = 0; i < GetSize(operands); ++i)
		field.branches[i].append(operands[i]);
}

void match_bitwise_fields(int offset, const std::vector<FactorBit> &bits,
		std::array<std::map<IdString, FactorField>, 2> &fields)
{
	pool<IdString> matched_types;
	for (const auto &seed : bits) {
		if (!seed.producer || !bitwise_type(seed.producer->type) || !matched_types.insert(seed.producer->type).second)
			continue;
		for (int variant = 0; variant < GetSize(fields); ++variant) {
			auto &field = fields[variant][seed.producer->type];
			field.type = seed.producer->type;
			int size = GetSize(field.offsets);
			match_bitwise_field(field, offset, bits, variant == 0 ? seed.a : seed.b);
			if (GetSize(field.offsets) == size && seed.a != seed.b)
				match_bitwise_field(field, offset, bits, variant == 0 ? seed.b : seed.a);
		}
	}
}

struct ChoiceFields
{
	std::map<std::vector<SigBit>, FactorField> nested;
	std::array<std::map<IdString, FactorField>, 2> bitwise;
	std::map<IdString, FactorField> reusable, single_operand;
};

ChoiceFields collect_fields(PmuxCoarseIndex &index, Cell *root, const FactorChoice &choice, const ChoiceColumns *available = nullptr)
{
	ChoiceFields fields;
	SigSpec output = index.port(root, ID::Y);
	pool<SigBit> outputs(output.begin(), output.end());
	dict<Cell *, FactorDriver> drivers;
	std::vector<FactorBit> bits;
	bits.reserve(choice.branches.size());
	for (int offset = 0; offset < GetSize(output); ++offset) {
		bits.clear();
		for (const auto &branch : choice.branches)
			bits.push_back(FactorBit::read(index, drivers, branch[offset]));
		if (available)
			match_reusable_field(index, root, outputs, offset, bits, *available, fields.reusable, fields.single_operand);
		match_nested_fields(offset, bits, fields.nested);
		match_bitwise_fields(offset, bits, fields.bitwise);
	}
	return fields;
}

struct ChoiceRewrite
{
	Cell *root;
	const FactorChoice *choice;
	std::vector<const FactorField *> fields;
};

bool apply_factor(PmuxCoarseIndex &index, const std::vector<ChoiceRewrite> &edits, bool require_reduction)
{
	PmuxRewrite rewrite(index.module, index, "factor choice fields");
	pool<Cell *> roots, region;
	for (const auto &[root, choice, fields] : edits) {
		roots.insert(root);
		region.insert(root);
		auto output = root->getPort(ID::Y);
		pool<int> factored;
		for (const auto *field : fields) {
			region.insert(field->producers.begin(), field->producers.end());
			SigSpec field_output;
			for (int offset : field->offsets) {
				log_assert(factored.insert(offset).second);
				field_output.append(output[offset]);
			}
			rewrite.connect(field_output, field->emit(&rewrite.staging, choice->select));
		}
		SigSpec remaining_output;
		std::vector<SigSpec> remaining_branches(choice->branches.size());
		for (int offset = 0; offset < GetSize(output); ++offset) {
			if (factored.count(offset))
				continue;
			remaining_output.append(output[offset]);
			for (int branch = 0; branch < GetSize(remaining_branches); ++branch)
				remaining_branches[branch].append(choice->branches[branch][offset]);
		}
		if (!remaining_output.empty())
			rewrite.connect(remaining_output, emit_choice(&rewrite.staging, choice->select, remaining_branches, root->type));
	}
	if (!prepare_factor(index, roots, region, rewrite) || (require_reduction && GetSize(rewrite.removed) <= rewrite.added_count()))
		return false;
	for (const auto &edit : edits)
		for (const auto *field : edit.fields)
			if (std::none_of(field->producers.begin(), field->producers.end(), [&](Cell *cell) { return rewrite.removed.count(cell); }))
				return false;
	if (!rewrite.validate())
		return false;
	rewrite.commit();
	return true;
}

bool factor_choice(PmuxCoarseIndex &index, Cell *root)
{
	auto choice = FactorChoice::read(index, root);
	if (!choice || !index.editable(root))
		return false;
	auto candidates = collect_fields(index, root, *choice);
	auto apply = [&](const std::vector<const FactorField *> &fields) { return apply_factor(index, {{root, &*choice, fields}}, false); };
	std::vector<const FactorField *> nested_fields;
	for (const auto &[conditions, field] : candidates.nested)
		nested_fields.push_back(&field);
	auto single_fields = nested_fields;
	const auto &bitwise = candidates.bitwise;
	for (int variant = 0; variant < GetSize(bitwise); ++variant) {
		if (variant == 1 && bitwise[0] == bitwise[1])
			break;
		auto fields = nested_fields;
		pool<int> occupied;
		for (const auto *field : fields)
			occupied.insert(field->offsets.begin(), field->offsets.end());
		for (const auto &[type, field] : bitwise[variant]) {
			if (field.offsets.empty())
				continue;
			if (variant == 0 || !(field == bitwise[0].at(type)))
				single_fields.push_back(&field);
			if (std::none_of(field.offsets.begin(), field.offsets.end(), [&](int offset) { return occupied.count(offset); })) {
				fields.push_back(&field);
				occupied.insert(field.offsets.begin(), field.offsets.end());
			}
		}
		if (GetSize(fields) > 1 && apply(fields))
			return true;
	}
	for (const auto *field : single_fields)
		if (apply({field}))
			return true;
	return false;
}

bool factor_joint_choices(PmuxCoarseIndex &index, const std::vector<IdString> &choices)
{
	using SelectKey = std::pair<IdString, SigSpec>;
	dict<SelectKey, ChoiceColumns> available;
	auto cells = index.module->cells().to_vector();
	std::sort(cells.begin(), cells.end(), [](auto a, auto b) { return a->name < b->name; });
	for (auto cell : cells)
		if (auto choice = FactorChoice::read(index, cell))
			available[{cell->type, choice->select}].add(index, cell, *choice);

	struct Candidate {
		Cell *root;
		FactorChoice choice;
		std::vector<FactorField> fields, single_operand;
		pool<Cell *> region;
		int reused;
	};
	std::vector<Candidate> candidates;
	dict<Cell *, std::vector<int>> readers;
	for (auto name : choices) {
		auto root = index.module->cell(name);
		if (!root || !index.editable(root))
			continue;
		auto choice = FactorChoice::read(index, root);
		if (!choice)
			continue;
		const auto &columns = available.at({root->type, choice->select});
		auto fields = collect_fields(index, root, *choice, columns.cells > 1 ? &columns : nullptr);
		Candidate candidate{root, std::move(*choice), {}, {}, {root}, 0};
		pool<int> occupied;
		auto append = [&](auto &group) {
			for (auto &[key, field] : group) {
				if (field.offsets.empty() || std::any_of(field.offsets.begin(), field.offsets.end(),
						[&](int offset) { return occupied.count(offset); }))
					continue;
				occupied.insert(field.offsets.begin(), field.offsets.end());
				candidate.region.insert(field.producers.begin(), field.producers.end());
				candidate.fields.push_back(std::move(field));
			}
		};
		append(fields.reusable);
		candidate.reused = GetSize(candidate.fields);
		append(fields.nested);
		for (auto &group : fields.bitwise)
			append(group);
		for (auto &[type, field] : fields.single_operand) {
			candidate.region.insert(field.producers.begin(), field.producers.end());
			candidate.single_operand.push_back(std::move(field));
		}
		if (candidate.fields.empty() && candidate.single_operand.empty())
			continue;
		for (auto producer : candidate.region)
			readers[producer].push_back(GetSize(candidates));
		candidates.push_back(std::move(candidate));
	}

	auto make_edit = [](const Candidate &candidate, bool include_single_operand, bool reused_only) {
		ChoiceRewrite edit{candidate.root, &candidate.choice, {}};
		pool<int> occupied;
		if (include_single_operand)
			for (const auto &field : candidate.single_operand) {
				edit.fields.push_back(&field);
				occupied.insert(field.offsets.begin(), field.offsets.end());
			}
		int count = reused_only ? candidate.reused : GetSize(candidate.fields);
		for (int i = 0; i < count; ++i) {
			const auto &field = candidate.fields[i];
			if (std::none_of(field.offsets.begin(), field.offsets.end(), [&](int offset) { return occupied.count(offset); }))
				edit.fields.push_back(&field);
		}
		return edit;
	};
	bool changed = false;
	pool<int> visited;
	pool<Cell *> grouped;
	for (int i = 0; i < GetSize(candidates); ++i) {
		if (!visited.insert(i).second)
			continue;
		std::vector<int> group{i};
		for (int j = 0; j < GetSize(group); ++j)
			for (auto producer : candidates[group[j]].region)
				if (grouped.insert(producer).second)
					for (int reader : readers.at(producer))
						if (visited.insert(reader).second)
							group.push_back(reader);

		auto apply_group = [&](bool include_single_operand) {
			std::vector<ChoiceRewrite> edits;
			for (int member : group) {
				auto edit = make_edit(candidates[member], include_single_operand, false);
				if (!edit.fields.empty())
					edits.push_back(std::move(edit));
			}
			return GetSize(edits) > 1 && apply_factor(index, edits, true);
		};
		bool has_single_operand = std::any_of(group.begin(), group.end(), [&](int member) {
			return !candidates[member].single_operand.empty();
		});
		if ((has_single_operand && apply_group(true)) || apply_group(false)) {
			changed = true;
			continue;
		}
		for (int member : group) {
			const auto &candidate = candidates[member];
			auto edit = make_edit(candidate, true, true);
			if (edit.fields.empty())
				continue;
			if (apply_factor(index, {edit}, true)) {
				changed = true;
				continue;
			}
			if (!candidate.single_operand.empty() && candidate.reused != 0)
				changed |= apply_factor(index, {make_edit(candidate, false, true)}, true);
		}
	}
	return changed;
}

bool reduction_type(IdString type)
{
	return type.in(ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor));
}

struct ReducedValue
{
	IdString type;
	SigSpec input;

	bool operator==(const ReducedValue &other) const { return type == other.type && input == other.input; }
	bool operator<(const ReducedValue &other) const { return std::tie(type, input) < std::tie(other.type, other.input); }
};

std::optional<ReducedValue> normalize_reduction(IdString type, const SigSpec &input)
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
			return ReducedValue{IdString(), bit};
		invert ^= parity && bit == State::S1;
	}
	if (remaining.empty())
		return ReducedValue{IdString(), SigSpec(and_gate || invert ? State::S1 : State::S0)};
	SigSpec operands;
	for (SigBit bit : remaining)
		operands.append(bit);
	if (GetSize(operands) == 1)
		return ReducedValue{invert ? ID($not) : IdString(), operands};
	if (parity)
		type = invert ? ID($reduce_xnor) : ID($reduce_xor);
	return ReducedValue{type, operands};
}

using ReductionResults = std::map<ReducedValue, std::vector<IdString>>;

void record_reduction(PmuxCoarseIndex &index, Cell *cell, ReductionResults &available)
{
	if (GetSize(cell->getPort(ID::Y)) != 1)
		return;
	auto input = index.port(cell, ID::A);
	if (cell->type == ID($not)) {
		if (GetSize(input) == 1)
			available[{ID($not), input}].push_back(cell->name);
		return;
	}
	auto value = normalize_reduction(cell->type, input);
	if (!value || value->type.empty())
		return;
	if (cell->type.in(ID($reduce_xor), ID($reduce_xnor))) {
		int wire_bits = 0;
		for (SigBit bit : input)
			wire_bits += bit.wire != nullptr;
		// 被抵消的重复位在原单元中仍可能传播未定义值。
		if (wire_bits != GetSize(value->input))
			return;
	}
	available[*value].push_back(cell->name);
}

std::optional<SigSpec> find_reduction(PmuxCoarseIndex &index, Cell *root, const ReducedValue &value,
		const ReductionResults &available)
{
	auto found = available.find(value);
	if (found == available.end())
		return std::nullopt;
	pool<SigBit> outputs{index.port(root, ID::Y).as_bit()};
	for (auto name : found->second) {
		auto cell = index.module->cell(name);
		if (!cell || cell == root)
			continue;
		auto output = index.port(cell, ID::Y);
		auto bit = output.as_bit();
		if (index.driver(bit) == cell && index.independent({bit}, outputs))
			return output;
	}
	return std::nullopt;
}

bool factor_reduction(PmuxCoarseIndex &index, Cell *root, ReductionResults &available)
{
	if (!index.editable(root) || GetSize(index.port(root, ID::Y)) != 1)
		return false;
	auto source = choice_input(index, index.port(root, ID::A));
	if (!source)
		return false;
	auto &[mux, choice] = *source;

	std::set<ReducedValue> unique;
	std::vector<ReducedValue> values;
	for (const auto &branch : choice.branches) {
		if (unspecified(branch)) {
			values.push_back({IdString(), SigSpec(State::Sx)});
			continue;
		}
		auto value = normalize_reduction(root->type, branch);
		if (!value)
			return false;
		values.push_back(*value);
		unique.insert(*value);
	}
	if (unique.empty())
		return false;

	PmuxRewrite candidate(index.module, index, "factor reduction");
	std::map<ReducedValue, SigSpec> results;
	std::vector<IdString> added;
	for (const auto &value : unique) {
		if (value.type.empty()) {
			results[value] = value.input;
			continue;
		}
		if (auto result = find_reduction(index, root, value, available)) {
			results[value] = *result;
			continue;
		}
		Wire *wire = candidate.staging.addWire(NEW_ID);
		Cell *reduction = candidate.staging.addCell(NEW_ID, value.type);
		reduction->setParam(ID::A_WIDTH, GetSize(value.input));
		reduction->setParam(ID::A_SIGNED, false);
		reduction->setParam(ID::Y_WIDTH, 1);
		reduction->setPort(ID::A, value.input);
		reduction->setPort(ID::Y, wire);
		results[value] = wire;
		added.push_back(reduction->name);
	}
	std::vector<SigSpec> branches;
	for (const auto &value : values)
		branches.push_back(unspecified(value.input) ? value.input : results.at(value));
	auto common = common_value(branches);
	candidate.connect(root->getPort(ID::Y), common ? *common : emit_choice(&candidate.staging, choice.select, branches));
	if (!prepare_factor(index, {root}, {root, mux}, candidate) ||
			((!added.empty() || !common) && !candidate.removed.count(mux)) || !candidate.validate())
		return false;
	candidate.commit();
	for (auto name : added)
		record_reduction(index, index.module->cell(name), available);
	return true;
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
		log_header(design, "Executing OPT_PMUX_FACTOR pass.\n");
		extra_args(args, 1, design);
		if (pmux_coarse_observes_undef(design))
			return;
		for (Module *module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			PmuxCoarseIndex index(module);
			ReductionResults available;
			std::vector<IdString> choices, reductions;
			for (Cell *cell : module->cells())
				if (reduction_type(cell->type) || cell->type == ID($not))
					record_reduction(index, cell, available);
			for (auto &[value, names] : available)
				std::sort(names.begin(), names.end());
			for (Cell *cell : module->selected_cells()) {
				if (cell->type.in(ID($mux), ID($pmux)))
					choices.push_back(cell->name);
				else if (reduction_type(cell->type))
					reductions.push_back(cell->name);
			}
			std::sort(reductions.begin(), reductions.end());
			std::sort(choices.begin(), choices.end());
			for (IdString name : reductions) {
				Cell *cell = module->cell(name);
				if (cell && factor_reduction(index, cell, available))
					design->scratchpad_set_bool("opt.did_something", true);
			}
			if (factor_joint_choices(index, choices))
				design->scratchpad_set_bool("opt.did_something", true);
			for (IdString name : choices) {
				Cell *cell = module->cell(name);
				if (cell && factor_choice(index, cell))
					design->scratchpad_set_bool("opt.did_something", true);
			}
		}
	}
} OptPmuxFactorPass;

PRIVATE_NAMESPACE_END

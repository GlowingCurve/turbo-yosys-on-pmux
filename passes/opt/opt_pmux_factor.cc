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
		if (select.empty() || GetSize(a) != width || GetSize(b) != width * GetSize(select))
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

SigSpec emit_choice(Module *module, const SigSpec &select, const std::vector<SigSpec> &values)
{
	if (auto common = common_value(values))
		return *common;
	SigSpec cases;
	for (int i = 1; i < GetSize(values); i++)
		cases.append(values[i]);
	return GetSize(select) == 1 ? module->Mux(NEW_ID, values.front(), cases, select)
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

bool prepare_factor(PmuxCoarseIndex &index, Cell *root, const pool<Cell *> &region, PmuxRewrite &rewrite)
{
	pool<SigBit> input_bits, output_bits;
	auto retain = [&](const SigSpec &input) {
		for (auto bit : input)
			if (bit.wire && bit.wire->module == index.module)
				input_bits.insert(bit);
	};
	for (Cell *cell : rewrite.staging.cells())
		for (const auto &[port, signal] : cell->connections())
			if (cell->input(port))
				retain(signal);
	for (const auto &connection : rewrite.staging.connections())
		retain(connection.second);
	for (auto bit : index.port(root, ID::Y))
		output_bits.insert(bit);
	rewrite.removed = index.removable(region, {}, output_bits, input_bits);
	return rewrite.removed.count(root);
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
		auto input = emit_choice(module, select, branches);
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

bool factor_choice(PmuxCoarseIndex &index, Cell *root)
{
	auto choice = FactorChoice::read(index, root);
	if (!choice || !index.editable(root))
		return false;
	SigSpec output = root->getPort(ID::Y);
	std::map<std::vector<SigBit>, FactorField> nested;
	std::array<std::map<IdString, FactorField>, 2> bitwise;
	dict<Cell *, FactorDriver> drivers;
	std::vector<FactorBit> bits;
	bits.reserve(choice->branches.size());
	for (int offset = 0; offset < GetSize(output); ++offset) {
		bits.clear();
		for (const auto &branch : choice->branches)
			bits.push_back(FactorBit::read(index, drivers, branch[offset]));
		match_nested_fields(offset, bits, nested);
		match_bitwise_fields(offset, bits, bitwise);
	}

	auto apply = [&](const std::vector<const FactorField *> &fields) {
		pool<Cell *> region{root};
		for (const auto *field : fields)
			region.insert(field->producers.begin(), field->producers.end());

		PmuxRewrite rewrite(index.module, index, "factor choice fields");
		pool<int> factored;
		for (const auto *field : fields) {
			SigSpec field_output;
			for (int offset : field->offsets) {
				factored.insert(offset);
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
			rewrite.connect(remaining_output, emit_choice(&rewrite.staging, choice->select, remaining_branches));
		if (!prepare_factor(index, root, region, rewrite))
			return false;
		for (const auto *field : fields)
			if (std::none_of(field->producers.begin(), field->producers.end(), [&](Cell *cell) { return rewrite.removed.count(cell); }))
				return false;
		if (!rewrite.validate())
			return false;
		rewrite.commit();
		return true;
	};
	std::vector<const FactorField *> nested_fields;
	for (const auto &[conditions, field] : nested)
		nested_fields.push_back(&field);
	auto single_fields = nested_fields;
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
	if (!prepare_factor(index, root, {root, mux}, candidate) ||
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
			for (IdString name : choices) {
				Cell *cell = module->cell(name);
				if (cell && factor_choice(index, cell))
					design->scratchpad_set_bool("opt.did_something", true);
			}
		}
	}
} OptPmuxFactorPass;

PRIVATE_NAMESPACE_END

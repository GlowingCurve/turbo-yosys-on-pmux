#include "kernel/log.h"
#include "kernel/register.h"
#include "pmux_coarse.h"

#include <algorithm>
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
		if (!cell->type.in(ID($mux), ID($pmux)) || !index.editable(cell))
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

Cell *whole_driver(PmuxCoarseIndex &index, const SigSpec &value)
{
	if (value.empty())
		return nullptr;
	Cell *cell = index.driver(value[0]);
	if (!cell || !cell->type.in(ID($mux), ID($pmux), ID($and), ID($or), ID($xor), ID($xnor)))
		return nullptr;
	return index.port(cell, ID::Y) == value && index.editable(cell) ? cell : nullptr;
}

pool<Cell *> profitable_removal(PmuxCoarseIndex &index, Cell *root, const pool<Cell *> &region,
		const std::vector<SigSpec> &inputs, int added)
{
	pool<SigBit> input_bits, output_bits;
	for (const auto &input : inputs)
		for (auto bit : input)
			input_bits.insert(bit);
	for (auto bit : index.port(root, ID::Y))
		output_bits.insert(bit);
	if (!index.independent(input_bits, output_bits))
		return {};
	auto removable = index.removable(region, {}, output_bits, input_bits);
	if (GetSize(removable) <= added || !removable.count(root))
		return {};
	return removable;
}

SigSpec remove_region(PmuxCoarseIndex &index, Cell *root, const pool<Cell *> &removable, int added)
{
	log("  Factoring selection at %s.%s (%d cells removed, %d added).\n",
		log_id(index.module), log_id(root), GetSize(removable), added);
	SigSpec output = root->getPort(ID::Y);
	for (Cell *cell : removable)
		index.module->remove(cell);
	return output;
}

bool factor_nested_choice(PmuxCoarseIndex &index, Cell *root, const FactorChoice &choice,
		const std::vector<Cell *> &drivers)
{
	Cell *seed = nullptr;
	for (Cell *driver : drivers)
		if (driver && driver->type == ID($mux)) {
			seed = driver;
			break;
		}
	if (!seed)
		return false;

	SigSpec a = index.port(seed, ID::A);
	SigSpec b = index.port(seed, ID::B);
	pool<Cell *> region{root};
	std::vector<SigSpec> conditions;
	for (int i = 0; i < GetSize(choice.branches); i++) {
		const SigSpec &branch = choice.branches[i];
		Cell *driver = drivers[i];
		if (unspecified(branch))
			conditions.emplace_back(State::Sx);
		else if (branch == a)
			conditions.emplace_back(State::S0);
		else if (branch == b)
			conditions.emplace_back(State::S1);
		else if (driver && driver->type == ID($mux) && index.port(driver, ID::A) == a && index.port(driver, ID::B) == b) {
			conditions.push_back(index.port(driver, ID::S));
			region.insert(driver);
		} else {
			return false;
		}
	}

	std::optional<SigSpec> common = common_value(conditions);
	std::vector<SigSpec> inputs = common ? std::vector<SigSpec>{*common} : conditions;
	if (!common)
		inputs.push_back(choice.select);
	inputs.push_back(a);
	inputs.push_back(b);
	int added = 1 + int(!common);
	auto removable = profitable_removal(index, root, region, inputs, added);
	if (removable.empty())
		return false;
	SigSpec output = remove_region(index, root, removable, added);
	SigSpec condition = emit_choice(index.module, choice.select, conditions);
	index.module->addMux(NEW_ID, a, b, condition, output);
	return true;
}

bool bitwise_type(IdString type)
{
	return type.in(ID($and), ID($or), ID($xor), ID($xnor));
}

std::pair<SigSpec, SigSpec> bitwise_operands(PmuxCoarseIndex &index, Cell *cell)
{
	int width = GetSize(index.port(cell, ID::Y));
	bool is_signed = cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
	SigSpec a = index.port(cell, ID::A);
	SigSpec b = index.port(cell, ID::B);
	a.extend_u0(width, is_signed);
	b.extend_u0(width, is_signed);
	return {a, b};
}

bool factor_bitwise(PmuxCoarseIndex &index, Cell *root, const FactorChoice &choice,
		const std::vector<Cell *> &drivers, IdString type, const SigSpec &common_operand)
{
	std::vector<SigSpec> operands;
	pool<Cell *> region{root};
	for (int i = 0; i < GetSize(choice.branches); i++) {
		const SigSpec &branch = choice.branches[i];
		if (unspecified(branch)) {
			operands.push_back(branch);
			continue;
		}
		if (branch == common_operand) {
			State identity = type.in(ID($and), ID($xnor)) ? State::S1 : State::S0;
			operands.emplace_back(identity, GetSize(branch));
			continue;
		}
		Cell *driver = drivers[i];
		if (!driver || driver->type != type)
			return false;
		auto [a, b] = bitwise_operands(index, driver);
		if (b == common_operand)
			std::swap(a, b);
		if (a != common_operand)
			return false;
		operands.push_back(b);
		region.insert(driver);
	}

	std::optional<SigSpec> common = common_value(operands);
	std::vector<SigSpec> inputs = common ? std::vector<SigSpec>{*common} : operands;
	if (!common)
		inputs.push_back(choice.select);
	inputs.push_back(common_operand);
	int added = 1 + int(!common);
	auto removable = profitable_removal(index, root, region, inputs, added);
	if (removable.empty())
		return false;
	SigSpec output = remove_region(index, root, removable, added);
	SigSpec operand = emit_choice(index.module, choice.select, operands);
	if (type == ID($and))
		index.module->addAnd(NEW_ID, common_operand, operand, output);
	else if (type == ID($or))
		index.module->addOr(NEW_ID, common_operand, operand, output);
	else if (type == ID($xor))
		index.module->addXor(NEW_ID, common_operand, operand, output);
	else
		index.module->addXnor(NEW_ID, common_operand, operand, output);
	return true;
}

bool factor_choice(PmuxCoarseIndex &index, Cell *root)
{
	auto choice = FactorChoice::read(index, root);
	if (!choice)
		return false;
	std::vector<Cell *> drivers;
	for (const auto &branch : choice->branches)
		drivers.push_back(whole_driver(index, branch));
	if (factor_nested_choice(index, root, *choice, drivers))
		return true;
	for (Cell *driver : drivers) {
		if (!driver || !bitwise_type(driver->type))
			continue;
		auto [a, b] = bitwise_operands(index, driver);
		return factor_bitwise(index, root, *choice, drivers, driver->type, a) ||
			factor_bitwise(index, root, *choice, drivers, driver->type, b);
	}
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

bool factor_reduction(PmuxCoarseIndex &index, Cell *root)
{
	if (!index.editable(root) || GetSize(index.port(root, ID::Y)) != 1)
		return false;
	SigSpec input = index.port(root, ID::A);
	Cell *mux = whole_driver(index, input);
	if (!mux)
		return false;
	auto choice = FactorChoice::read(index, mux);
	if (!choice)
		return false;

	std::set<ReducedValue> unique;
	std::vector<ReducedValue> values;
	for (const auto &branch : choice->branches) {
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
	bool select = GetSize(unique) > 1;
	int added = int(select);
	std::vector<SigSpec> inputs;
	for (const auto &value : unique) {
		inputs.push_back(value.input);
		added += !value.type.empty();
	}
	if (select)
		inputs.push_back(choice->select);
	auto removable = profitable_removal(index, root, {root, mux}, inputs, added);
	if (removable.empty())
		return false;

	SigSpec output = remove_region(index, root, removable, added);
	std::map<ReducedValue, SigSpec> results;
	for (const auto &value : unique) {
		if (value.type.empty()) {
			results[value] = value.input;
			continue;
		}
		Wire *wire = index.module->addWire(NEW_ID);
		Cell *reduction = index.module->addCell(NEW_ID, value.type);
		reduction->setParam(ID::A_WIDTH, GetSize(value.input));
		reduction->setParam(ID::A_SIGNED, false);
		reduction->setParam(ID::Y_WIDTH, 1);
		reduction->setPort(ID::A, value.input);
		reduction->setPort(ID::Y, wire);
		results[value] = wire;
	}
	std::vector<SigSpec> branches;
	for (const auto &value : values)
		branches.push_back(unspecified(value.input) ? value.input : results.at(value));
	index.module->connect(output, emit_choice(index.module, choice->select, branches));
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
		log("Factor common bitwise operations or nested muxes across selections,\n");
		log("and move reductions to their input branches when this removes RTLIL cells.\n");
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
			std::vector<IdString> choices, reductions;
			for (Cell *cell : module->selected_cells()) {
				if (cell->type.in(ID($mux), ID($pmux)))
					choices.push_back(cell->name);
				else if (reduction_type(cell->type))
					reductions.push_back(cell->name);
			}
			for (IdString name : reductions) {
				Cell *cell = module->cell(name);
				if (cell && factor_reduction(index, cell))
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

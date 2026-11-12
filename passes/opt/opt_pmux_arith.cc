#include "kernel/log.h"
#include "kernel/register.h"
#include "pmux_coarse.h"

#include <algorithm>
#include <map>
#include <set>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ArithmeticExpression
{
	std::map<SigSpec, int> terms;
	Const offset;

	explicit ArithmeticExpression(int width) : offset(0, width) {}
};

struct ArithmeticColumn
{
	std::vector<SigSpec> values;
	bool selected;
	bool subtract;
};

using ArithmeticPlan = std::vector<ArithmeticColumn>;

bool arithmetic_type(IdString type)
{
	return type.in(ID($add), ID($sub), ID($neg));
}

SigSpec trim_zero_extension(SigSpec value)
{
	int width = GetSize(value);
	while (width > 1 && value[width - 1] == State::S0)
		width--;
	return value.extract(0, width);
}

struct BinaryArithmeticInputs
{
	PmuxCoarseIndex &index;
	bool external_inputs;
	int remaining = 65536;
	pool<Cell *> active;
	dict<Cell *, bool> checked;

	BinaryArithmeticInputs(PmuxCoarseIndex &index, bool external_inputs) : index(index), external_inputs(external_inputs) {}

	bool check(const SigSpec &value, int depth = 0)
	{
		if (depth > 128)
			return false;
		for (SigBit bit : value) {
			if (--remaining < 0)
				return false;
			if (!bit.wire) {
				if (bit != State::S0 && bit != State::S1)
					return false;
				continue;
			}
			Cell *driver = index.driver(bit);
			if (driver ? !check_driver(driver, depth) : !(external_inputs && index.module_input(bit)))
				return false;
		}
		return true;
	}

	bool check_driver(Cell *cell, int depth)
	{
		if (checked.count(cell))
			return checked.at(cell);
		if (!cell->type.in(ID($add), ID($sub), ID($neg), ID($mul), ID($not), ID($and), ID($or), ID($xor), ID($xnor),
				ID($eq), ID($ne), ID($lt), ID($le), ID($gt), ID($ge), ID($logic_not), ID($logic_and), ID($logic_or),
				ID($reduce_and), ID($reduce_or), ID($reduce_bool), ID($reduce_xor), ID($reduce_xnor),
				ID($mux), ID($slice), ID($concat)) || !active.insert(cell).second)
			return false;
		bool defined = true;
		for (const auto &[name, input] : cell->connections())
			if (cell->input(name) && !check(index.sigmap(input), depth + 1)) {
				defined = false;
				break;
			}
		active.erase(cell);
		checked[cell] = defined;
		return defined;
	}
};

struct ArithmeticRewrite
{
	PmuxCoarseIndex &index;
	int width;
	int remaining = 2048;
	pool<Cell *> region;
	bool full_width_result = false;

	ArithmeticRewrite(PmuxCoarseIndex &index, int width) : index(index), width(width) {}

	bool expand(SigSpec value, int sign, ArithmeticExpression &expression, int depth = 0)
	{
		if (--remaining < 0 || depth > 12 || GetSize(expression.terms) > 16)
			return false;
		if (value.is_fully_const()) {
			if (!value.is_fully_def())
				return false;
			expression.offset = sign > 0 ? const_add(expression.offset, value.as_const(), false, false, width)
				: const_sub(expression.offset, value.as_const(), false, false, width);
			return true;
		}

		Cell *driver = index.driver(value[0]);
		if (driver && arithmetic_type(driver->type) && index.editable(driver)) {
			SigSpec a = index.port(driver, ID::A);
			SigSpec b;
			bool is_signed = driver->getParam(ID::A_SIGNED).as_bool();
			if (driver->type != ID($neg)) {
				b = index.port(driver, ID::B);
				is_signed &= driver->getParam(ID::B_SIGNED).as_bool();
			}
			SigSpec output = index.port(driver, ID::Y);
			const int output_width = GetSize(output);
			const int compared_width = std::min(output_width, width);
			bool matches = output.extract(0, compared_width) == value.extract(0, compared_width);
			if (output_width < width) {
				// A narrowed result can be widened only when the original operation cannot overflow.
				bool signed_extension = is_signed;
				bool zero_extension = !is_signed && driver->type == ID($add);
				matches &= (signed_extension || zero_extension) && output_width > std::max(GetSize(a), GetSize(b));
				output.extend_u0(width, signed_extension);
				matches &= output == value;
			}
			if (matches) {
				if (depth == 0)
					full_width_result = output_width >= width;
				region.insert(driver);
				a.extend_u0(width, is_signed);
				if (driver->type == ID($neg))
					return expand(a, -sign, expression, depth + 1);
				b.extend_u0(width, is_signed);
				return expand(a, sign, expression, depth + 1) &&
					expand(b, driver->type == ID($sub) ? -sign : sign, expression, depth + 1);
			}
		}

		for (SigBit bit : value)
			if (!bit.wire && bit != State::S0 && bit != State::S1)
				return false;
		value = trim_zero_extension(value);
		int &coefficient = expression.terms[value];
		coefficient += sign;
		if (coefficient == 0)
			expression.terms.erase(value);
		return true;
	}
};

void add_column(ArithmeticPlan &plan, const std::vector<SigSpec> &values, const std::vector<bool> &defined, bool subtract)
{
	SigSpec common;
	int width = 0;
	bool same = true;
	for (int i = 0; i < GetSize(values); i++) {
		if (!defined[i])
			continue;
		width = std::max(width, GetSize(values[i]));
		if (common.empty())
			common = values[i];
		same &= values[i] == common;
	}
	if (same) {
		if (!common.is_fully_zero())
			plan.push_back({{common}, false, subtract});
		return;
	}

	ArithmeticColumn column{{}, true, subtract};
	for (int i = 0; i < GetSize(values); i++) {
		SigSpec value = defined[i] ? values[i] : SigSpec(State::Sx, width);
		value.extend_u0(width);
		column.values.push_back(value);
	}
	plan.push_back(std::move(column));
}

ArithmeticPlan make_column_plan(std::vector<ArithmeticExpression> expressions, const std::vector<bool> &defined)
{
	ArithmeticPlan plan;
	for (int sign : {1, -1}) {
		// Emit common terms before allocating selector inputs to the remaining terms.
		int first = std::find(defined.begin(), defined.end(), true) - defined.begin();
		for (auto [term, coefficient] : expressions[first].terms) {
			int common = coefficient * sign;
			for (int i = 0; i < GetSize(expressions) && common > 0; i++) {
				if (!defined[i])
					continue;
				auto entry = expressions[i].terms.find(term);
				common = entry == expressions[i].terms.end() ? 0 : std::min(common, entry->second * sign);
			}
			for (int n = 0; n < common; n++)
				plan.push_back({{term}, false, sign < 0});
			if (common > 0)
				for (int i = 0; i < GetSize(expressions); i++)
					if (defined[i])
						expressions[i].terms.at(term) -= common * sign;
		}

		std::vector<std::vector<SigSpec>> terms(GetSize(expressions));
		int count = 0;
		for (int i = 0; i < GetSize(expressions); i++) {
			for (auto &[term, coefficient] : expressions[i].terms)
				for (int n = 0; n < coefficient * sign; n++)
					terms[i].push_back(term);
			count = std::max(count, GetSize(terms[i]));
		}
		for (int j = 0; j < count; j++) {
			std::vector<SigSpec> values;
			for (auto &branch : terms)
				values.push_back(j < GetSize(branch) ? branch[j] : SigSpec(State::S0));
			add_column(plan, values, defined, sign < 0);
		}
	}

	std::vector<SigSpec> offsets;
	for (auto &expression : expressions)
		offsets.push_back(trim_zero_extension(expression.offset));
	add_column(plan, offsets, defined, false);
	return plan;
}

ArithmeticPlan make_exclusion_plan(const std::vector<ArithmeticExpression> &expressions, const std::vector<bool> &defined,
		BinaryArithmeticInputs &binary)
{
	std::set<SigSpec> total;
	std::vector<SigSpec> offsets;
	for (int i = 0; i < GetSize(expressions); i++) {
		offsets.push_back(trim_zero_extension(expressions[i].offset));
		if (!defined[i])
			continue;
		for (auto &[term, coefficient] : expressions[i].terms) {
			if (coefficient != 1)
				return {};
			total.insert(term);
		}
	}
	if (GetSize(total) < 3)
		return {};
	// The total includes terms unused by individual branches. They must be binary
	// so an unknown term cannot contaminate a branch that originally omitted it.
	for (const auto &term : total)
		if (!binary.check(term))
			return {};

	std::vector<SigSpec> excluded(GetSize(expressions), State::S0);
	for (int i = 0; i < GetSize(expressions); i++) {
		if (!defined[i])
			continue;
		if (GetSize(expressions[i].terms) != GetSize(total) - 1)
			return {};
		for (const auto &term : total)
			if (!expressions[i].terms.count(term)) {
				excluded[i] = term;
				break;
			}
	}

	ArithmeticPlan plan;
	for (const auto &term : total)
		plan.push_back({{term}, false, false});
	add_column(plan, excluded, defined, true);
	add_column(plan, offsets, defined, false);
	return plan;
}

struct ArithmeticCost
{
	pool<Cell *> remove;
	int added = 0;
	int selected_bits = 0;
	int gain() const { return GetSize(remove) - added; }
};

ArithmeticCost cost_plan(PmuxCoarseIndex &index, const pool<Cell *> &region, const SigSpec &output,
		const SigSpec &select, const ArithmeticPlan &plan)
{
	ArithmeticCost cost;
	pool<SigBit> inputs;
	pool<SigBit> outputs;
	bool has_positive_term = false;
	for (const auto &column : plan) {
		has_positive_term |= !column.subtract;
		if (column.selected) {
			cost.added++;
			cost.selected_bits += GetSize(column.values.front());
			for (auto bit : select)
				inputs.insert(bit);
		}
		for (const auto &value : column.values)
			for (auto bit : value)
				inputs.insert(bit);
	}
	cost.added += GetSize(plan) - int(has_positive_term);
	for (auto bit : output)
		outputs.insert(bit);
	if (index.independent(inputs, outputs))
		cost.remove = index.removable(region, {}, outputs, inputs);
	return cost;
}

SigSpec emit_arithmetic(Module *module, const ArithmeticPlan &plan, const SigSpec &select, int width)
{
	SigSpec result(State::S0);
	bool has_result = false;
	for (bool subtract : {false, true}) {
		for (const auto &column : plan) {
			if (column.subtract != subtract)
				continue;
			SigSpec operand = column.values.front();
			if (column.selected) {
				SigSpec cases;
				for (int i = 1; i < GetSize(column.values); i++)
					cases.append(column.values[i]);
				if (GetSize(select) == 1)
					operand = module->Mux(NEW_ID, operand, cases, select);
				else
					operand = module->Pmux(NEW_ID, operand, cases, select);
			}
			if (has_result || subtract) {
				SigSpec sum(module->addWire(NEW_ID, width));
				if (subtract)
					module->addSub(NEW_ID, result, operand, sum);
				else
					module->addAdd(NEW_ID, result, operand, sum);
				result = sum;
			} else {
				result = operand;
			}
			has_result = true;
		}
	}
	result.extend_u0(width);
	return result;
}

bool rewrite_arithmetic(PmuxCoarseIndex &index, Cell *root, bool external_inputs)
{
	if (!index.editable(root))
		return false;
	SigSpec output = index.port(root, ID::Y);
	int width = GetSize(output);
	ArithmeticRewrite rewrite{index, width};
	BinaryArithmeticInputs binary{index, external_inputs};
	SigSpec select;
	std::vector<SigSpec> branches;
	if (arithmetic_type(root->type)) {
		branches.push_back(output);
	} else {
		select = index.port(root, ID::S);
		SigSpec data = index.port(root, ID::B);
		if (select.empty() || GetSize(select) > 64 || GetSize(data) != width * GetSize(select))
			return false;
		branches.push_back(index.port(root, ID::A));
		for (int i = 0; i < GetSize(select); i++)
			branches.push_back(data.extract(i * width, width));
		if (std::none_of(branches.begin(), branches.end(), [&](const SigSpec &branch) {
			Cell *driver = branch.empty() ? nullptr : index.driver(branch[0]);
			return driver && arithmetic_type(driver->type);
		}))
			return false;
		// A binary mux merges its branches bit by bit for an unknown selector.
		// Selecting an arithmetic operand before its operation may lose known bits.
		if (root->type == ID($mux) && !binary.check(select))
			return false;
	}

	std::vector<ArithmeticExpression> expressions;
	std::vector<bool> defined;
	for (const SigSpec &branch : branches) {
		if (GetSize(branch) != width)
			return false;
		expressions.emplace_back(width);
		bool unspecified = branch.is_fully_const() && branch.as_const().is_fully_undef_x_only();
		defined.push_back(!unspecified);
		if (unspecified)
			continue;
		rewrite.full_width_result = false;
		if (!rewrite.expand(branch, 1, expressions.back()))
			return false;
		// Full-width arithmetic is all X when an input is unknown. An unexpanded
		// or zero-extended branch may still have defined bits in that situation.
		if (!select.empty() && !rewrite.full_width_result && !binary.check(branch))
			return false;
	}
	if (rewrite.region.empty())
		return false;
	rewrite.region.insert(root);

	ArithmeticPlan plan = make_column_plan(expressions, defined);
	ArithmeticCost cost = cost_plan(index, rewrite.region, output, select, plan);
	if (GetSize(select) >= 2) {
		ArithmeticPlan exclusion = make_exclusion_plan(expressions, defined, binary);
		if (!exclusion.empty()) {
			ArithmeticCost alternative = cost_plan(index, rewrite.region, output, select, exclusion);
			if (alternative.gain() > cost.gain() ||
					(alternative.gain() == cost.gain() && alternative.selected_bits < cost.selected_bits)) {
				plan = std::move(exclusion);
				cost = std::move(alternative);
			}
		}
	}
	if (cost.gain() <= 0 || !cost.remove.count(root))
		return false;

	log("  Rewriting arithmetic at %s.%s (%d cells removed, %d added).\n",
		log_id(index.module), log_id(root), GetSize(cost.remove), cost.added);
	SigSpec target = root->getPort(ID::Y);
	for (auto cell : cost.remove)
		index.module->remove(cell);
	SigSpec result = emit_arithmetic(index.module, plan, select, width);
	index.module->connect(target, result);
	return true;
}

struct OptPmuxArithPass : public Pass
{
	OptPmuxArithPass() : Pass("opt_pmux_arith", "simplify and share modular arithmetic around selections") {}

	void help() override
	{
		log("\n");
		log("    opt_pmux_arith [selection]\n");
		log("\n");
		log("Simplify additions and subtractions modulo the result width and share\n");
		log("arithmetic across $mux and $pmux branches when this removes RTLIL cells.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing OPT_PMUX_ARITH pass.\n");
		extra_args(args, 1, design);
		if (pmux_coarse_observes_undef(design))
			return;
		pool<IdString> instantiated;
		for (Module *module : design->modules())
			for (Cell *cell : module->cells())
				if (design->module(cell->type))
					instantiated.insert(cell->type);
		for (Module *module : design->selected_modules()) {
			if (module->has_processes_warn())
				continue;
			PmuxCoarseIndex index(module);
			std::vector<IdString> selections, operators;
			for (Cell *cell : module->selected_cells()) {
				if (cell->type.in(ID($mux), ID($pmux)))
					selections.push_back(cell->name);
				else if (arithmetic_type(cell->type))
					operators.push_back(cell->name);
			}
			selections.insert(selections.end(), operators.begin(), operators.end());
			bool external_inputs = !instantiated.count(module->name);
			for (IdString name : selections) {
				Cell *cell = module->cell(name);
				if (cell && rewrite_arithmetic(index, cell, external_inputs))
					design->scratchpad_set_bool("opt.did_something", true);
			}
		}
	}
} OptPmuxArithPass;

PRIVATE_NAMESPACE_END

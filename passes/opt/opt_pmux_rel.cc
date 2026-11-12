#include "kernel/yosys.h"
#include "passes/opt/pmux_coarse.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Parity {
	std::vector<SigBit> terms;
	bool inverted = false;
	bool undef = false;

	bool operator==(const Parity &) const = default;
	Hasher hash_into(Hasher hash) const
	{
		hash.eat(terms);
		hash.eat(inverted);
		hash.eat(undef);
		return hash;
	}
};

Parity difference(const Parity &a, const Parity &b)
{
	Parity result;
	result.undef = a.undef || b.undef;
	if (!result.undef) {
		result.inverted = a.inverted != b.inverted;
		std::set_symmetric_difference(a.terms.begin(), a.terms.end(), b.terms.begin(), b.terms.end(), std::back_inserter(result.terms));
	}
	return result;
}

struct Column {
	SigBit output;
	std::vector<Parity> rows;
	int term_count = 0;
	int inversions = 0;
	int reference = -1;
	Parity delta;
};

struct Selection {
	Cell *cell;
	std::vector<Column> columns;
};

class RelationWorker
{
	Module *module;
	PmuxCoarseIndex index;

	struct Operands {
		SigSpec a, b;
	};
	dict<Cell *, Operands> operators;

	std::optional<Parity> literal(SigBit bit) const
	{
		if (bit.wire)
			return Parity{{bit}};
		if (bit == State::S0 || bit == State::S1)
			return Parity{{}, bit == State::S1};
		if (bit == State::Sx)
			return Parity{{}, false, true};
		return std::nullopt;
	}

	std::optional<Parity> expression(SigBit bit, pool<Cell *> &region)
	{
		auto source = index.source(bit);
		if (!source || source->port != ID::Y || !source->cell->type.in(ID($xor), ID($xnor), ID($not)))
			return literal(bit);
		auto cell = source->cell;
		auto entry = operators.emplace(cell, Operands{});
		if (entry.second) {
			auto &operands = entry.first->second;
			int width = GetSize(cell->getPort(ID::Y));
			if (width > 4096)
				return literal(bit);
			operands.a = index.port(cell, ID::A);
			bool sign = cell->getParam(ID::A_SIGNED).as_bool();
			if (cell->type != ID($not)) {
				operands.b = index.port(cell, ID::B);
				sign &= cell->getParam(ID::B_SIGNED).as_bool();
				operands.b.extend_u0(width, sign);
			}
			operands.a.extend_u0(width, sign);
		}
		const auto &operands = entry.first->second;
		if (operands.a.empty())
			return literal(bit);
		auto a = literal(operands.a[source->offset]);
		auto b = cell->type == ID($not) ? literal(State::S0) : literal(operands.b[source->offset]);
		if (!a || !b || (!a->terms.empty() && a->terms == b->terms))
			return literal(bit);
		auto result = difference(*a, *b);
		if (!result.undef)
			result.inverted ^= cell->type != ID($xor);
		region.insert(cell);
		return result;
	}

	static const Parity *first_value(const Column &column)
	{
		for (const auto &row : column.rows)
			if (!row.undef)
				return &row;
		return nullptr;
	}

	static bool usable_relation(const Column &base, const Column &other, const Parity &delta)
	{
		// 保留目标分支的数据依赖，避免为目标引入额外的未定义输入。
		for (int row = 0; row < GetSize(other.rows); ++row) {
			const auto &value = other.rows[row];
			if (value.undef)
				continue;
			const auto &terms = base.rows[row].terms;
			if (!std::includes(value.terms.begin(), value.terms.end(), terms.begin(), terms.end()) ||
					!std::includes(value.terms.begin(), value.terms.end(), delta.terms.begin(), delta.terms.end()))
				return false;
		}
		return true;
	}

	int rewrite(const SigSpec &control, const std::vector<IdString> &names, IdString type)
	{
		operators.clear();
		std::vector<Selection> selections;
		std::vector<Column *> columns;
		pool<Cell *> candidates, replaced;
		int rows = GetSize(control) + 1;
		int inspected = 0;
		for (auto name : names) {
			auto cell = module->cell(name);
			if (!cell || !index.editable(cell) || index.port(cell, ID::S) != control)
				continue;
			SigSpec a = index.port(cell, ID::A), b = index.port(cell, ID::B), y = index.port(cell, ID::Y);
			int width = GetSize(y);
			if (width > 4096 || GetSize(a) != width || GetSize(b) != (rows - 1) * width)
				continue;
			inspected += rows * width;
			if (inspected > 65536)
				break;
			auto &selection = selections.emplace_back(Selection{cell, {}});
			for (int offset = 0; offset < width; ++offset) {
				auto &column = selection.columns.emplace_back();
				column.output = y[offset];
				for (int row = 0; row < rows; ++row) {
					auto value = expression(row == 0 ? a[offset] : b[(row - 1) * width + offset], candidates);
					if (!value) {
						column.rows.clear();
						break;
					}
				column.term_count += GetSize(value->terms);
				column.inversions += value->inverted;
					column.rows.push_back(std::move(*value));
				}
			}
			for (auto &column : selection.columns)
				columns.push_back(&column);
		}
		std::stable_sort(columns.begin(), columns.end(), [](const Column *a, const Column *b) {
			return std::tie(a->term_count, a->inversions) < std::tie(b->term_count, b->inversions);
		});
		dict<std::vector<Parity>, std::vector<int>> groups;
		for (int col = 0; col < GetSize(columns); ++col) {
			auto &column = *columns[col];
			auto first = first_value(column);
			if (!first)
				continue;
			std::vector<Parity> signature;
			for (const auto &row : column.rows)
				signature.push_back(difference(row, *first));
			auto &bases = groups[signature];
			for (int base : bases) {
				auto delta = difference(*first_value(*columns[base]), *first);
				if (usable_relation(*columns[base], column, delta)) {
					column.reference = base;
					column.delta = std::move(delta);
					break;
				}
			}
			if (column.reference == -1 && GetSize(bases) < 32)
				bases.push_back(col);
		}
		struct MuxPlan {
			SigSpec a, b, y;
		};
		std::vector<MuxPlan> muxes;
		pool<SigBit> inputs, outputs;
		for (const auto &selection : selections) {
			if (std::none_of(selection.columns.begin(), selection.columns.end(), [](const Column &col) { return col.reference >= 0; }))
				continue;
			auto cell = selection.cell;
			candidates.insert(cell);
			replaced.insert(cell);
			SigSpec a = index.port(cell, ID::A), b = index.port(cell, ID::B);
			int width = GetSize(selection.columns);
			std::vector<int> kept;
			MuxPlan plan;
			for (int offset = 0; offset < width; ++offset) {
				const auto &column = selection.columns[offset];
				outputs.insert(column.output);
				if (column.reference < 0) {
					kept.push_back(offset);
					plan.a.append(a[offset]);
					plan.y.append(column.output);
				}
			}
			for (int row = 0; row < rows - 1; ++row)
				for (int offset : kept)
					plan.b.append(b[row * width + offset]);
			if (!plan.y.empty()) {
				inputs.insert(plan.a.begin(), plan.a.end());
				inputs.insert(plan.b.begin(), plan.b.end());
				muxes.push_back(std::move(plan));
			}
		}
		if (replaced.empty())
			return 0;
		if (!muxes.empty())
			inputs.insert(control.begin(), control.end());
		struct ParityPlan {
			std::vector<SigSpec> operands;
			SigSpec y;
		};
		dict<std::pair<int, bool>, ParityPlan> relations;
		for (auto column : columns) {
			if (column->reference < 0)
				continue;
			auto base = columns[column->reference]->output;
			if (!outputs.count(base))
				inputs.insert(base);
			const auto &delta = column->delta;
			inputs.insert(delta.terms.begin(), delta.terms.end());
			int terms = GetSize(delta.terms);
			auto &relation = relations[{terms, delta.inverted}];
			relation.operands.resize(terms + 1);
			relation.operands[0].append(base);
			for (int term = 0; term < terms; ++term)
				relation.operands[term + 1].append(delta.terms[term]);
			relation.y.append(column->output);
		}
		int added = GetSize(muxes);
		for (const auto &[form, relation] : relations)
			added += std::max(form.first, int(form.second));
		auto remove = index.removable(candidates, {}, outputs, inputs);
		for (auto cell : replaced)
			if (!remove.count(cell))
				return 0;
		if (GetSize(remove) <= added || !index.independent(inputs, outputs))
			return 0;
		for (auto cell : remove)
			module->remove(cell);
		for (const auto &mux : muxes) {
			if (type == ID($mux))
				module->addMux(NEW_ID, mux.a, mux.b, control, mux.y);
			else
				module->addPmux(NEW_ID, mux.a, mux.b, control, mux.y);
		}
		for (const auto &[form, relation] : relations) {
			const auto &[terms, inverted] = form;
			SigSpec left = relation.operands[0];
			if (!terms) {
				if (inverted)
					module->addNot(NEW_ID, left, relation.y);
				else
					module->connect(relation.y, left);
			}
			for (int term = 1; term <= terms; ++term) {
				bool final = term == terms;
				SigSpec right = relation.operands[term];
				SigSpec output = final ? relation.y : SigSpec(module->addWire(NEW_ID, GetSize(relation.y)));
				if (final && inverted)
					module->addXnor(NEW_ID, left, right, output);
				else
					module->addXor(NEW_ID, left, right, output);
				left = output;
			}
		}
		return GetSize(remove) - added;
	}

public:
	explicit RelationWorker(Module *module) : module(module), index(module) {}

	void run()
	{
		dict<std::pair<IdString, SigSpec>, std::vector<IdString>> groups;
		for (auto cell : module->selected_cells()) {
			if (!cell->type.in(ID($mux), ID($pmux)))
				continue;
			SigSpec select = index.port(cell, ID::S);
			if (select.empty() || GetSize(select) > 32)
				continue;
			groups[{cell->type, select}].push_back(cell->name);
		}
		int saved = 0;
		for (const auto &[key, cells] : groups)
			saved += rewrite(index.sigmap(key.second), cells, key.first);
		if (saved)
			log("  %s: shared selection output relations, removed %d net cells.\n", log_id(module), saved);
	}
};

struct OptPmuxRelPass : Pass {
	OptPmuxRelPass() : Pass("opt_pmux_rel", "share identical, complementary, and XOR-related selection outputs") {}

	void help() override
	{
		log("    opt_pmux_rel [selection]\n\n");
		log("Share corresponding output columns of muxes with equal selectors when their\n");
		log("data is identical or differs by a branch-independent XOR and RTLIL cell count decreases.\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		extra_args(args, 1, design);
		log_header(design, "Executing OPT_PMUX_REL pass.\n");
		if (pmux_coarse_observes_undef(design))
			return;
		for (auto module : design->selected_modules())
			if (module->processes.empty())
				RelationWorker(module).run();
	}
} OptPmuxRelPass;

PRIVATE_NAMESPACE_END

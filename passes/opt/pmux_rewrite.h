#ifndef YOSYS_PMUX_REWRITE_H
#define YOSYS_PMUX_REWRITE_H

#include "passes/opt/pmux_coarse.h"

YOSYS_NAMESPACE_BEGIN

class PmuxRewrite
{
	Module *module;
	const PmuxCoarseIndex &index;
	const char *rule;
	bool validated = false;

	SigBit canonical(SigBit bit) const
	{
		return bit.wire && bit.wire->module == module ? index.sigmap(bit) : bit;
	}

	struct CandidateDriver {
		Cell *cell;
		SigBit alias;
	};

	bool independent_bit(SigBit bit, const dict<SigBit, CandidateDriver> &drivers,
			pool<SigBit> &inputs, pool<SigBit> &active, pool<SigBit> &checked,
			pool<Cell *> &checked_cells, pool<Cell *> &active_cells) const
	{
		bit = canonical(bit);
		if (!bit.wire || checked.count(bit))
			return true;
		if (!active.insert(bit).second)
			return false;

		auto driver = drivers.find(bit);
		if (driver == drivers.end()) {
			if (bit.wire->module != module)
				return false;
			inputs.insert(bit);
		} else if (auto cell = driver->second.cell) {
			if (!checked_cells.count(cell)) {
				if (!active_cells.insert(cell).second)
					return false;
				for (const auto &[name, signal] : cell->connections()) {
					if (cell->port_dir(name) != RTLIL::PD_INPUT || !PmuxCoarseIndex::combinational_input(cell->type, name))
						continue;
					for (auto input : signal)
						if (!independent_bit(input, drivers, inputs, active, checked, checked_cells, active_cells))
							return false;
				}
				active_cells.erase(cell);
				checked_cells.insert(cell);
			}
		} else if (!independent_bit(driver->second.alias, drivers, inputs, active, checked, checked_cells, active_cells)) {
			return false;
		}

		active.erase(bit);
		checked.insert(bit);
		return true;
	}

	bool check_removal(const std::vector<Cell *> &added) const
	{
		pool<SigBit> outputs, retained;
		dict<SigBit, CandidateDriver> drivers;
		auto add_driver = [&](SigBit bit, CandidateDriver driver) {
			bit = canonical(bit);
			if (!bit.wire || !drivers.emplace(bit, driver).second)
				return false;
			if (bit.wire->module == &staging)
				return true;
			if (bit.wire->module != module)
				return false;
			auto old = index.source(bit);
			if (!old || !removed.count(old->cell))
				return false;
			outputs.insert(bit);
			return true;
		};
		auto retain = [&](SigBit bit) {
			bit = canonical(bit);
			if (bit.wire && bit.wire->module == module && !outputs.count(bit))
				retained.insert(bit);
		};
		for (auto cell : added)
			for (const auto &[name, signal] : cell->connections()) {
				auto direction = cell->port_dir(name);
				if (direction == RTLIL::PD_INPUT)
					continue;
				if (direction != RTLIL::PD_OUTPUT)
					return false;
				for (auto bit : signal)
					if (!add_driver(bit, {cell, SigBit()}))
						return false;
			}
		for (const auto &[lhs, rhs] : staging.connections())
			for (int i = 0; i < GetSize(lhs); ++i)
				if (!add_driver(lhs[i], {nullptr, rhs[i]}))
					return false;
		for (auto cell : added)
			for (const auto &[name, signal] : cell->connections())
				if (cell->port_dir(name) == RTLIL::PD_INPUT)
					for (auto bit : signal)
						retain(bit);
		for (const auto &connection : staging.connections())
			for (auto bit : connection.second)
				retain(bit);

		if (index.removable(removed, {}, outputs, retained) != removed)
			return false;
		pool<SigBit> inputs, active, checked;
		pool<Cell *> checked_cells, active_cells;
		for (auto bit : outputs)
			if (!independent_bit(bit, drivers, inputs, active, checked, checked_cells, active_cells))
				return false;
		return index.independent(inputs, outputs);
	}

public:
	Module staging;
	pool<Cell *> removed;

	PmuxRewrite(Module *module, const PmuxCoarseIndex &index, const char *rule) : module(module), index(index), rule(rule) {}

	void connect(const SigSpec &lhs, const SigSpec &rhs) { staging.connect(lhs, rhs); }
	int added_count() const { return staging.cells_size(); }

	bool validate()
	{
		log_assert(!validated);
		validated = check_removal(staging.cells().to_vector());
		return validated;
	}

	void commit()
	{
		log_assert(validated);
		dict<Wire *, Wire *> wires;
		for (auto wire : staging.wires())
			wires.emplace(wire, module->addWire(wire->name, wire));
		auto remap = [&](const SigSpec &signal) {
			SigSpec result;
			for (const auto &chunk : signal.chunks()) {
				if (chunk.wire && chunk.wire->module == &staging)
					result.append(SigSpec(wires.at(chunk.wire), chunk.offset, chunk.width));
				else
					result.append(chunk);
			}
			return result;
		};
		for (auto cell : removed)
			module->remove(cell);
		for (auto cell : staging.cells()) {
			auto replacement = module->addCell(cell->name, cell->type);
			replacement->attributes = cell->attributes;
			replacement->parameters = cell->parameters;
			for (const auto &[name, signal] : cell->connections())
				replacement->setPort(name, remap(signal));
		}
		for (const auto &[lhs, rhs] : staging.connections())
			module->connect(remap(lhs), remap(rhs));
		log_debug("PMUX %s in %s: committed.\n", rule, log_id(module));
	}
};

YOSYS_NAMESPACE_END

#endif

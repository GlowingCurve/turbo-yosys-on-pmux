#ifndef YOSYS_PMUX_REWRITE_H
#define YOSYS_PMUX_REWRITE_H

#include "passes/opt/pmux_coarse.h"

YOSYS_NAMESPACE_BEGIN

class PmuxRewrite
{
	Module *module;
	PmuxCoarseIndex &index;
	const char *rule;
	bool validated = false;
	pool<Cell *> removed_cells;

	struct RemovalBoundary {
		pool<SigBit> outputs, inputs;
		size_t revision;
	};
	std::optional<RemovalBoundary> removal_boundary;

	SigBit canonical(SigBit bit) const
	{
		return bit.wire && bit.wire->module == module ? index.sigmap(bit) : bit;
	}

	bool staged_boundary(pool<SigBit> &outputs, pool<SigBit> &retained, PmuxCoarseIndex::Drivers &drivers)
	{
		auto add_driver = [&](SigBit bit, PmuxCoarseIndex::Driver driver) {
			bit = canonical(bit);
			if (!bit.wire)
				return false;
			log_assert(bit.wire->module == module || bit.wire->module == &staging);
			if (!drivers.emplace(bit, driver).second)
				return false;
			if (bit.wire->module == module)
				outputs.insert(bit);
			return true;
		};
		auto retain = [&](SigBit bit) {
			bit = canonical(bit);
			if (bit.wire && bit.wire->module == module)
				retained.insert(bit);
		};
		for (auto cell : staging.cells()) {
			for (const auto &[name, signal] : cell->connections()) {
				auto direction = cell->port_dir(name);
				log_assert(direction == RTLIL::PD_INPUT || direction == RTLIL::PD_OUTPUT);
				for (auto bit : signal) {
					if (direction == RTLIL::PD_INPUT)
						retain(bit);
					else if (!add_driver(bit, {cell, SigBit()}))
						return false;
				}
			}
		}
		for (const auto &[lhs, rhs] : staging.connections()) {
			for (int i = 0; i < GetSize(lhs); ++i) {
				if (!add_driver(lhs[i], {nullptr, rhs[i]}))
					return false;
				retain(rhs[i]);
			}
		}
		for (auto bit : outputs)
			retained.erase(bit);
		return true;
	}

	bool check_removal()
	{
		pool<SigBit> outputs, retained;
		PmuxCoarseIndex::Drivers drivers;
		if (!staged_boundary(outputs, retained, drivers))
			return false;
		for (auto bit : outputs) {
			auto old = index.source(bit);
			if (!old || !removed.count(old->cell))
				return false;
		}

		bool checked_removal = removal_boundary && removal_boundary->revision == index.revision() &&
				removal_boundary->outputs == outputs && removal_boundary->inputs == retained;
		if (!checked_removal && !std::all_of(removed.begin(), removed.end(), [&](Cell *cell) {
				return index.can_remove(cell, removed, {}, outputs, retained);
			}))
			return false;
		return index.independent_rewrite(outputs, drivers);
	}

public:
	Module staging;
	const pool<Cell *> &removed = removed_cells;

	PmuxRewrite(Module *module, PmuxCoarseIndex &index, const char *rule) : module(module), index(index), rule(rule)
	{
		log_assert(module == index.module && module->design);
	}
	PmuxRewrite(const PmuxRewrite &) = delete;
	PmuxRewrite &operator=(const PmuxRewrite &) = delete;

	void find_removable(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users,
			const pool<SigBit> &outputs, const pool<SigBit> &inputs)
	{
		log_assert(!validated);
		RemovalBoundary boundary{index.normalize_bits(outputs), index.normalize_bits(inputs), index.revision()};
		removed_cells = index.removable_normalized(candidates, replaced_users, boundary.outputs, boundary.inputs);
		removal_boundary.reset();
		// 只有已删除的使用者才可在最终验证时忽略。
		if (std::all_of(replaced_users.begin(), replaced_users.end(), [&](auto cell) { return removed.count(cell); }))
			removal_boundary.emplace(std::move(boundary));
	}
	void find_removable(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users = {}, const pool<SigBit> &outputs = {})
	{
		log_assert(!validated);
		pool<SigBit> staged_outputs, retained;
		PmuxCoarseIndex::Drivers drivers;
		if (!staged_boundary(staged_outputs, retained, drivers)) {
			removed_cells.clear();
			removal_boundary.reset();
			return;
		}
		find_removable(candidates, replaced_users, outputs.empty() ? staged_outputs : outputs, retained);
	}

	void connect(const SigSpec &lhs, const SigSpec &rhs) { staging.connect(lhs, rhs); }
	int added_count() const { return staging.cells_size(); }

	bool validate()
	{
		log_assert(!validated);
		validated = check_removal();
		removal_boundary.reset();
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
		auto design = module->design;
		bool inherit_selection = !removed.empty() && !design->selected_whole_module(module->name);
		for (auto cell : removed)
			module->remove(cell);
		for (auto cell : staging.cells()) {
			auto replacement = module->addCell(cell->name, cell->type);
			replacement->attributes = cell->attributes;
			replacement->parameters = cell->parameters;
			for (const auto &[name, signal] : cell->connections())
				replacement->setPort(name, remap(signal));
			if (inherit_selection)
				design->select(module, replacement);
		}
		for (const auto &[lhs, rhs] : staging.connections())
			module->connect(remap(lhs), remap(rhs));
		log_debug("PMUX %s in %s: committed.\n", rule, log_id(module));
	}
};

YOSYS_NAMESPACE_END

#endif

#ifndef YOSYS_PMUX_COARSE_H
#define YOSYS_PMUX_COARSE_H

#include "passes/opt/pmux_common.h"

YOSYS_NAMESPACE_BEGIN

class PmuxCoarseIndex
{
	struct Index : ModIndex {
		bool aliases_changed = true;
		bool blacked_out = false;
		size_t revision = 0;

		explicit Index(Module *module) : ModIndex(module) {}

		void notify_connect(Cell *cell, IdString port, const SigSpec &old_sig, const SigSpec &sig) override
		{
			ModIndex::notify_connect(cell, port, old_sig, sig);
			++revision;
		}

		void notify_connect(Module *module, const RTLIL::SigSig &connection) override
		{
			if (auto_reload_module)
				sigmap.add(connection.first, connection.second);
			else
				ModIndex::notify_connect(module, connection);
			aliases_changed = true;
			++revision;
		}

		void notify_connect(Module *module, const std::vector<RTLIL::SigSig> &connections) override
		{
			ModIndex::notify_connect(module, connections);
			// RTLIL notifies monitors before replacing the module's connection list.
			sigmap.clear();
			for (const auto &[lhs, rhs] : connections)
				sigmap.add(lhs, rhs);
			aliases_changed = true;
			++revision;
		}

		void notify_blackout(Module *module) override
		{
			ModIndex::notify_blackout(module);
			sigmap.set(module);
			aliases_changed = true;
			blacked_out = true;
			++revision;
		}
	};

	Index index;
	std::optional<std::vector<Wire *>> protected_wires;
	pool<SigBit> kept_bits, inout_bits;
	size_t cache_revision = 0;
	struct BitInfo {
		std::optional<ModIndex::PortInfo> source;
		bool input = false;
	};
	dict<SigBit, BitInfo> bit_cache;
	dict<std::pair<Cell *, IdString>, bool> editable_cache;

	void refresh_caches()
	{
		if (cache_revision == index.revision)
			return;
		bit_cache.clear();
		editable_cache.clear();
		cache_revision = index.revision;
	}

	void refresh_protected_bits()
	{
		if (!protected_wires || index.blacked_out) {
			index.blacked_out = false;
			protected_wires.emplace();
			for (auto wire : module->wires())
				if (wire->get_bool_attribute(ID::keep) || (wire->port_input && wire->port_output))
					protected_wires->push_back(wire);
		}
		if (!index.aliases_changed)
			return;
		kept_bits.clear();
		inout_bits.clear();
		for (auto wire : *protected_wires) {
			bool keep = wire->get_bool_attribute(ID::keep);
			bool inout = wire->port_input && wire->port_output;
			for (auto bit : sigmap(wire)) {
				if (!bit.wire)
					continue;
				if (keep)
					kept_bits.insert(bit);
				if (inout)
					inout_bits.insert(bit);
			}
		}
		index.aliases_changed = false;
	}

	bool editable_cell(Cell *cell) const
	{
		return module->design->selected(module, cell) && !cell->get_bool_attribute(ID::keep);
	}

	bool editable_output(Cell *cell, IdString name, int offset, SigBit bit)
	{
		auto driver = source(bit);
		if (!driver || driver->cell != cell || driver->port != name || driver->offset != offset)
			return false;
		refresh_protected_bits();
		return !kept_bits.count(bit);
	}

public:
	using Port = ModIndex::PortInfo;
	struct Driver {
		Cell *cell;
		SigBit alias;
	};
	using Drivers = dict<SigBit, Driver>;
	Module *const module;
	const SigMap &sigmap;

	explicit PmuxCoarseIndex(Module *module) : index(module), module(module), sigmap(index.sigmap) {}
	PmuxCoarseIndex(const PmuxCoarseIndex &) = delete;
	PmuxCoarseIndex &operator=(const PmuxCoarseIndex &) = delete;

	SigSpec port(Cell *cell, IdString name) const { return sigmap(cell->getPort(name)); }

	size_t revision() const { return index.revision; }

	std::optional<Port> source(SigBit bit)
	{
		return bit_info(bit).source;
	}

	Cell *driver(SigBit bit)
	{
		auto found = source(bit);
		return found ? found->cell : nullptr;
	}

	bool module_input(SigBit bit)
	{
		return bit_info(bit).input;
	}

	bool editable(Cell *cell, IdString name = ID::Y)
	{
		log_assert(cell->module == module);
		refresh_caches();
		auto key = std::make_pair(cell, name);
		if (auto found = editable_cache.find(key); found != editable_cache.end())
			return found->second;
		bool result = find_editable(cell, name);
		editable_cache.emplace(key, result);
		return result;
	}

	// replaced_users 的旧输入连接会移除，新增或保留的输入必须纳入 retained_inputs。
	// replaced_outputs 由新逻辑驱动，其原有使用者仍可读取该信号。
	pool<Cell *> removable(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users,
			const pool<SigBit> &replaced_outputs, const pool<SigBit> &retained_inputs)
	{
		return removable_normalized(candidates, replaced_users, normalize_bits(replaced_outputs), normalize_bits(retained_inputs));
	}

	bool independent(const pool<SigBit> &inputs, const pool<SigBit> &outputs)
	{
		return outputs.empty() || trace(inputs, normalize_bits(outputs), nullptr, nullptr);
	}

	bool independent_rewrite(const pool<SigBit> &outputs, const Drivers &drivers)
	{
		pool<SigBit> inputs;
		return trace(outputs, {}, &drivers, &inputs) && independent(inputs, outputs);
	}

private:
	BitInfo bit_info(SigBit bit)
	{
		if (!bit.wire || bit.wire->module != module)
			return {};
		refresh_caches();
		if (auto found = bit_cache.find(bit); found != bit_cache.end())
			return found->second;
		BitInfo result;
		const auto *info = index.query(bit);
		if (info) {
			if (info->is_input) {
				refresh_protected_bits();
				result.input = !inout_bits.count(sigmap(bit));
			}
			for (const auto &port : info->ports) {
				auto direction = port.cell->port_dir(port.port);
				if (direction == RTLIL::PD_INPUT)
					continue;
				if (info->is_input || direction != RTLIL::PD_OUTPUT || result.source) {
					result = {};
					break;
				}
				result.source = port;
			}
		}
		bit_cache.emplace(bit, result);
		return result;
	}

	bool find_editable(Cell *cell, IdString name)
	{
		if (!editable_cell(cell) || !cell->hasPort(name) || cell->port_dir(name) != RTLIL::PD_OUTPUT)
			return false;
		auto output = port(cell, name);
		for (int offset = 0; offset < GetSize(output); ++offset)
			if (!editable_output(cell, name, offset, output[offset]))
				return false;
		return !output.empty();
	}

public:
	pool<SigBit> normalize_bits(const pool<SigBit> &bits) const
	{
		pool<SigBit> normalized;
		for (auto bit : bits)
			normalized.insert(sigmap(bit));
		return normalized;
	}

	pool<Cell *> removable_normalized(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users,
			const pool<SigBit> &replaced, const pool<SigBit> &retained)
	{
		pool<Cell *> result = candidates;
		std::vector<Cell *> blocked;
		for (auto cell : result)
			if (!can_remove(cell, result, replaced_users, replaced, retained))
				blocked.push_back(cell);

		pool<SigBit> checked;
		pool<Cell *> next;
		while (!blocked.empty()) {
			for (auto cell : blocked)
				result.erase(cell);
			if (result.empty())
				break;
			for (auto cell : blocked) {
				if (replaced_users.count(cell))
					continue;
				for (const auto &[port, signal] : cell->connections()) {
					if (cell->port_dir(port) != RTLIL::PD_INPUT)
						continue;
					for (auto bit : sigmap(signal)) {
						if (!bit.wire || replaced.count(bit) || !checked.insert(bit).second)
							continue;
						if (auto producer = driver(bit); producer && result.count(producer))
							next.insert(producer);
					}
				}
			}
			blocked.clear();
			// Revisit producers in the current candidate sequence. Membership alone does not order the work.
			for (auto cell : result) {
				if (next.erase(cell))
					blocked.push_back(cell);
				if (next.empty())
					break;
			}
		}
		return result;
	}

	bool can_remove(Cell *cell, const pool<Cell *> &candidates, const pool<Cell *> &replaced_users,
			const pool<SigBit> &replaced_outputs, const pool<SigBit> &retained_inputs)
	{
		if (!editable_cell(cell) || (!yosys_celltypes.cell_evaluable(cell->type) && !StaticCellTypes::categories.is_ff(cell->type)))
			return false;
		bool has_output = false;
		for (const auto &[name, signal] : cell->connections()) {
			auto direction = cell->port_dir(name);
			if (direction == RTLIL::PD_INPUT)
				continue;
			if (direction != RTLIL::PD_OUTPUT)
				return false;
			auto output = sigmap(signal);
			for (int offset = 0; offset < GetSize(output); ++offset) {
				has_output = true;
				auto bit = output[offset];
				if (retained_inputs.count(bit) || !editable_output(cell, name, offset, bit))
					return false;
				if (replaced_outputs.count(bit))
					continue;
				const auto *info = index.query(bit);
				log_assert(info);
				if (info->is_output)
					return false;
				for (const auto &port : info->ports)
					if (!candidates.count(port.cell) && !replaced_users.count(port.cell))
						return false;
			}
		}
		return has_output;
	}

private:
	struct Traversal {
		const pool<SigBit> &targets;
		const Drivers *drivers;
		pool<SigBit> *inputs;
		pool<SigBit> checked, active_bits;
		pool<Cell *> active, visited;
		int remaining = 65536;

		Traversal(const pool<SigBit> &targets, const Drivers *drivers, pool<SigBit> *inputs) :
				targets(targets), drivers(drivers), inputs(inputs) {}
	};

	bool trace(const pool<SigBit> &roots, const pool<SigBit> &targets, const Drivers *drivers, pool<SigBit> *inputs)
	{
		Traversal traversal(targets, drivers, inputs);
		return std::all_of(roots.begin(), roots.end(), [&](SigBit bit) { return independent_bit(bit, traversal, 0); });
	}

	bool independent_bit(SigBit bit, Traversal &walk, int depth)
	{
		if (bit.wire && bit.wire->module == module)
			bit = sigmap(bit);
		if (walk.targets.count(bit))
			return false;
		if (!bit.wire || walk.checked.count(bit))
			return true;
		if (--walk.remaining < 0 || depth > 128)
			return false;

		Cell *cell = nullptr;
		if (walk.drivers) {
			auto candidate = walk.drivers->find(bit);
			if (candidate == walk.drivers->end()) {
				if (bit.wire->module != module)
					return false;
				walk.inputs->insert(bit);
			} else if (!(cell = candidate->second.cell)) {
				if (!walk.active_bits.insert(bit).second || !independent_bit(candidate->second.alias, walk, depth + 1))
					return false;
				walk.active_bits.erase(bit);
			}
		} else {
			auto existing = bit_info(bit);
			if (existing.source)
				cell = existing.source->cell;
			else if (!existing.input)
				return false;
		}
		if (cell && !walk.visited.count(cell)) {
			if (!walk.active.insert(cell).second)
				return false;
			for (const auto &[name, signal] : cell->connections()) {
				auto direction = cell->port_dir(name);
				if (direction != RTLIL::PD_INPUT && direction != RTLIL::PD_OUTPUT)
					return false;
				if (direction == RTLIL::PD_OUTPUT || !pmux_combinational_input(cell->type, name))
					continue;
				for (auto input : signal)
					if (!independent_bit(input, walk, depth + 1))
						return false;
			}
			walk.active.erase(cell);
			walk.visited.insert(cell);
		}
		walk.checked.insert(bit);
		return true;
	}
};

YOSYS_NAMESPACE_END

#endif

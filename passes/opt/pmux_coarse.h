#ifndef YOSYS_PMUX_COARSE_H
#define YOSYS_PMUX_COARSE_H

#include "kernel/modtools.h"

#include <algorithm>
#include <optional>

YOSYS_NAMESPACE_BEGIN

inline bool pmux_coarse_observes_undef(Design *design)
{
	// 子模块中变化的未定义值也可能由调用模块观察。
	for (auto module : design->modules())
		for (auto cell : module->cells())
			if (cell->type.in(ID($eqx), ID($nex), ID($bweqx)) || StaticCellTypes::categories.is_tristate(cell->type))
				return true;
	return false;
}

class PmuxCoarseIndex
{
	friend class PmuxRewrite;

	struct Index : ModIndex {
		bool aliases_changed = true;
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
			aliases_changed = true;
			++revision;
		}

		void notify_blackout(Module *module) override
		{
			ModIndex::notify_blackout(module);
			aliases_changed = true;
			++revision;
		}
	};

	mutable Index index;
	mutable std::optional<std::vector<Wire *>> protected_wires;
	mutable pool<SigBit> kept_bits, inout_bits;

	void refresh_protected_bits() const
	{
		if (!protected_wires) {
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

	bool editable_output(Cell *cell, IdString name, int offset, SigBit bit) const
	{
		auto driver = source(bit);
		if (!driver || driver->cell != cell || driver->port != name || driver->offset != offset)
			return false;
		refresh_protected_bits();
		return !kept_bits.count(bit);
	}

public:
	static bool combinational_input(IdString type, IdString port)
	{
		if (type.in(ID($ff), ID($dff), ID($dffe), ID($sdff), ID($sdffe), ID($sdffce)))
			return false;
		if (type.in(ID($adff), ID($adffe)))
			return port == ID::ARST;
		if (type.in(ID($aldff), ID($aldffe)))
			return port.in(ID::ALOAD, ID::AD);
		if (type.in(ID($dffsr), ID($dffsre)))
			return port.in(ID::SET, ID::CLR);
		return true;
	}

	using Port = ModIndex::PortInfo;
	Module *const module;
	const SigMap &sigmap;

	explicit PmuxCoarseIndex(Module *module) : index(module), module(module), sigmap(index.sigmap) {}
	PmuxCoarseIndex(const PmuxCoarseIndex &) = delete;
	PmuxCoarseIndex &operator=(const PmuxCoarseIndex &) = delete;

	SigSpec port(Cell *cell, IdString name) const { return sigmap(cell->getPort(name)); }

	std::optional<std::pair<SigSpec, SigSpec>> comparison_operands(Cell *cell, int max_width) const
	{
		log_assert(cell->type.in(ID($eq), ID($ne), ID($logic_not)));
		bool unary = cell->type == ID($logic_not);
		auto a = port(cell, ID::A);
		auto b = unary ? SigSpec(State::S0, GetSize(a)) : port(cell, ID::B);
		int width = std::max(GetSize(a), GetSize(b));
		if (width > max_width)
			return std::nullopt;
		bool is_signed = !unary && cell->getParam(ID::A_SIGNED).as_bool() && cell->getParam(ID::B_SIGNED).as_bool();
		a.extend_u0(width, is_signed);
		b.extend_u0(width, is_signed);
		return std::make_pair(std::move(a), std::move(b));
	}

	std::optional<Port> source(SigBit bit) const
	{
		if (!bit.wire)
			return std::nullopt;
		const auto *info = index.query(bit);
		if (!info || info->is_input)
			return std::nullopt;
		std::optional<Port> driver;
		for (const auto &port : info->ports) {
			auto direction = port.cell->port_dir(port.port);
			if (direction == RTLIL::PD_INPUT)
				continue;
			if (direction != RTLIL::PD_OUTPUT || driver)
				return std::nullopt;
			driver = port;
		}
		return driver;
	}

	Cell *driver(SigBit bit) const
	{
		auto found = source(bit);
		return found ? found->cell : nullptr;
	}

	bool module_input(SigBit bit) const
	{
		const auto *info = index.query(bit);
		if (!info || !info->is_input)
			return false;
		refresh_protected_bits();
		return !inout_bits.count(sigmap(bit)) && std::all_of(info->ports.begin(), info->ports.end(), [](const auto &port) {
			return port.cell->port_dir(port.port) == RTLIL::PD_INPUT;
		});
	}

	bool editable(Cell *cell, IdString name = ID::Y) const
	{
		if (!editable_cell(cell) || !cell->hasPort(name) || cell->port_dir(name) != RTLIL::PD_OUTPUT)
			return false;
		auto output = port(cell, name);
		for (int offset = 0; offset < GetSize(output); ++offset)
			if (!editable_output(cell, name, offset, output[offset]))
				return false;
		return !output.empty();
	}

	// replaced_users 的旧输入连接会移除，新增或保留的输入必须纳入 retained_inputs。
	// replaced_outputs 由新逻辑驱动，其原有使用者仍可读取该信号。
	pool<Cell *> removable(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users,
			const pool<SigBit> &replaced_outputs, const pool<SigBit> &retained_inputs) const
	{
		return removable_normalized(candidates, replaced_users, normalize_bits(replaced_outputs), normalize_bits(retained_inputs));
	}

	bool independent(const pool<SigBit> &inputs, const pool<SigBit> &outputs) const
	{
		if (inputs.empty() || outputs.empty())
			return true;
		pool<SigBit> targets, checked;
		pool<Cell *> active, visited;
		for (auto bit : outputs)
			targets.insert(sigmap(bit));
		int remaining = 65536;
		for (auto bit : inputs)
			if (!independent_bit(bit, targets, checked, active, visited, remaining, 0))
				return false;
		return true;
	}

private:
	pool<SigBit> normalize_bits(const pool<SigBit> &bits) const
	{
		pool<SigBit> normalized;
		for (auto bit : bits)
			normalized.insert(sigmap(bit));
		return normalized;
	}

	pool<Cell *> removable_normalized(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users,
			const pool<SigBit> &replaced, const pool<SigBit> &retained) const
	{
		pool<Cell *> result = candidates;
		std::vector<Cell *> blocked;
		for (auto cell : result)
			if (!can_remove(cell, result, replaced_users, replaced, retained))
				blocked.push_back(cell);

		pool<SigBit> checked_inputs;
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
					// 非输入端口会使该信号失去唯一驱动，无法阻止可删除的生产者。
					if (cell->port_dir(port) != RTLIL::PD_INPUT)
						continue;
					for (auto bit : signal) {
						bit = sigmap(bit);
						if (!bit.wire || replaced.count(bit) || !checked_inputs.insert(bit).second)
							continue;
						if (auto producer = driver(bit); producer && result.count(producer))
							next.insert(producer);
					}
				}
			}
			blocked.assign(next.begin(), next.end());
			next.clear();
			// pool 删除元素时会移动尾部元素，按当前遍历顺序处理每轮删除。
			const auto &ordered = result;
			std::sort(blocked.begin(), blocked.end(), [&](Cell *left, Cell *right) {
				return left != right && ordered.count(right, ordered.find(left));
			});
		}
		return result;
	}

	bool all_removable(const pool<Cell *> &cells, const pool<SigBit> &outputs, const pool<SigBit> &inputs) const
	{
		return std::all_of(cells.begin(), cells.end(), [&](auto cell) {
			return can_remove(cell, cells, {}, outputs, inputs);
		});
	}

	bool can_remove(Cell *cell, const pool<Cell *> &candidates, const pool<Cell *> &replaced_users,
			const pool<SigBit> &replaced_outputs, const pool<SigBit> &retained_inputs) const
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
				if (info->is_output)
					return false;
				for (const auto &port : info->ports)
					if (!candidates.count(port.cell) && !replaced_users.count(port.cell))
						return false;
			}
		}
		return has_output;
	}

	bool independent_bit(SigBit bit, const pool<SigBit> &targets, pool<SigBit> &checked, pool<Cell *> &active,
			pool<Cell *> &visited, int &remaining, int depth) const
	{
		bit = sigmap(bit);
		if (targets.count(bit))
			return false;
		if (!bit.wire || checked.count(bit))
			return true;
		if (--remaining < 0 || depth > 128)
			return false;

		const auto *info = index.query(bit);
		if (!info)
			return false;
		if (info->is_input) {
			if (!module_input(bit))
				return false;
		} else {
			auto driver = source(bit);
			if (!driver)
				return false;
			auto cell = driver->cell;
			if (!visited.count(cell)) {
				if (!active.insert(cell).second)
					return false;
				for (const auto &[name, signal] : cell->connections()) {
					auto direction = cell->port_dir(name);
					if (direction == RTLIL::PD_OUTPUT)
						continue;
					if (direction != RTLIL::PD_INPUT)
						return false;
					if (!combinational_input(cell->type, name))
						continue;
					for (auto input : signal)
						if (!independent_bit(input, targets, checked, active, visited, remaining, depth + 1))
							return false;
				}
				active.erase(cell);
				visited.insert(cell);
			}
		}
		checked.insert(bit);
		return true;
	}
};

YOSYS_NAMESPACE_END

#endif

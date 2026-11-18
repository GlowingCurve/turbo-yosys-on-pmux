/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  薛朝意
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

// 基础设施层的模块网表索引。跟踪信号别名与单元连接，检查网表改写是否会破坏原有驱动或形成组合环路。

#ifndef YOSYS_PMUX_COARSE_H
#define YOSYS_PMUX_COARSE_H

#include "passes/opt/pmux_common.h"
#include <memory>

YOSYS_NAMESPACE_BEGIN

// 跟踪模块连接变化，使驱动信息及保护属性能够随网表更新。
struct PmuxConnectivity : ModIndex {
	bool aliases_changed = true;
	bool blacked_out = false;
	size_t revision = 0;
	std::optional<std::vector<Wire *>> protected_wires;
	pool<SigBit> kept_bits, inout_bits;
	size_t cache_revision = 0;
	// 记录单个信号位的模块输入属性及唯一驱动。
	struct BitInfo {
		std::optional<ModIndex::PortInfo> source;
		bool input = false;
	};
	dict<SigBit, BitInfo> bit_cache;
	dict<std::pair<Cell *, IdString>, bool> editable_cache;

	// 建立模块连接索引并开始接收网表变化通知。
	explicit PmuxConnectivity(Module *module) : ModIndex(module) {}

	// 更新单元端口连接并使相关查询缓存失效。
	void notify_connect(Cell *cell, IdString port, const SigSpec &old_sig, const SigSpec &sig) override
	{
		ModIndex::notify_connect(cell, port, old_sig, sig);
		++revision;
	}

	// 加入新的信号别名并记录连接变化。
	void notify_connect(Module *module, const RTLIL::SigSig &connection) override
	{
		if (auto_reload_module)
			sigmap.add(connection.first, connection.second);
		else
			ModIndex::notify_connect(module, connection);
		aliases_changed = true;
		++revision;
	}

	// 按新的完整连接表重建别名关系。
	void notify_connect(Module *module, const std::vector<RTLIL::SigSig> &connections) override
	{
		ModIndex::notify_connect(module, connections);
		// RTLIL 在替换模块连接表之前发出通知，此处使用通知中的新连接。
		sigmap.clear();
		for (const auto &[lhs, rhs] : connections)
			sigmap.add(lhs, rhs);
		aliases_changed = true;
		++revision;
	}

	// 模块连接失效时重新建立信号映射。
	void notify_blackout(Module *module) override
	{
		ModIndex::notify_blackout(module);
		sigmap.set(module);
		aliases_changed = true;
		blacked_out = true;
		++revision;
	}
};

// 查询模块内的单元、驱动和使用者，检查改写边界。
class PmuxCoarseIndex
{
      public:
	using Port = ModIndex::PortInfo;
	// 表示驱动暂存信号的单元或直接连线。
	struct Driver {
		Cell *cell;
		SigBit alias;
	};
	using Drivers = dict<SigBit, Driver>;
	Module *const module;
	const SigMap &sigmap;

	// 在同一模块的各项优化间共享连接索引。
	explicit PmuxCoarseIndex(Module *module) : PmuxCoarseIndex(module, std::make_shared<PmuxConnectivity>(module)) {}
	// 副本继续使用同一份模块连接索引和查询缓存。
	PmuxCoarseIndex(const PmuxCoarseIndex &) = default;
	PmuxCoarseIndex &operator=(const PmuxCoarseIndex &) = delete;

	// 读取经过别名归一化的端口信号。
	SigSpec port(Cell *cell, IdString name) const { return sigmap(cell->getPort(name)); }

	// 根据运算的符号属性，将端口扩展到目标位宽。
	SigSpec extended_port(Cell *cell, IdString name, int width, bool is_signed) const
	{
		auto value = port(cell, name);
		value.extend_u0(width, is_signed);
		return value;
	}

	// 读取指定位置的数据位，超过端口宽度时读取扩展位。
	SigBit port_bit(Cell *cell, IdString name, int offset, bool is_signed) const
	{
		const auto &value = cell->getPort(name);
		if (offset < GetSize(value))
			return sigmap(value[offset]);
		return is_signed && !value.empty() ? sigmap(value[GetSize(value) - 1]) : SigBit(State::S0);
	}

	// 返回最近一次网表变化的版本号。
	size_t revision() const { return state->revision; }

	// 查找信号位的唯一驱动端口。
	std::optional<Port> source(SigBit bit) const { return bit_info(bit).source; }

	// 取得驱动单元，供调用方继续追溯。
	Cell *driver(SigBit bit) const
	{
		auto found = source(bit);
		return found ? found->cell : nullptr;
	}

	// 区分普通输入与可能由内部驱动的双向端口。
	bool module_input(SigBit bit) { return bit_info(bit).input; }

	// 检查单元选择状态、唯一驱动及输出保护属性。
	bool editable(Cell *cell, IdString name = ID::Y)
	{
		log_assert(cell->module == module);
		refresh_caches();
		auto key = std::make_pair(cell, name);
		auto found = state->editable_cache.find(key);
		if (found != state->editable_cache.end())
			return found->second;
		bool result = find_editable(cell, name);
		state->editable_cache.emplace(key, result);
		return result;
	}

	// replaced_users 的旧输入连接会移除，新增或保留的输入必须纳入 retained_inputs。
	// replaced_outputs 由新逻辑驱动，其原有使用者仍可读取该信号。
	pool<Cell *> removable(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users, const pool<SigBit> &replaced_outputs,
			       const pool<SigBit> &retained_inputs)
	{
		return removable_normalized(candidates, replaced_users, normalize_bits(replaced_outputs), normalize_bits(retained_inputs));
	}

	// 检查所需输入是否依赖将被替换的输出。
	bool independent(const pool<SigBit> &inputs, const pool<SigBit> &outputs)
	{
		return outputs.empty() || comb_independent(inputs, normalize_bits(outputs));
	}

	// 检查暂存电路内部和原模块边界两侧的组合路径。
	bool independent_rewrite(const pool<SigBit> &outputs, const Drivers &drivers)
	{
		pool<SigBit> inputs;
		return collect_staged_inputs(outputs, drivers, inputs) && independent(inputs, outputs);
	}

	// 将一组可能含别名的信号转换为模块内的代表位。
	pool<SigBit> normalize_bits(const pool<SigBit> &bits) const
	{
		pool<SigBit> normalized;
		for (auto bit : bits)
			normalized.insert(sigmap(bit));
		return normalized;
	}

	// 从候选集合中依次剔除仍被使用的单元。
	pool<Cell *> removable_normalized(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users, const pool<SigBit> &replaced,
					  const pool<SigBit> &retained)
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
						auto producer = driver(bit);
						if (producer && result.count(producer))
							next.insert(producer);
					}
				}
			}
			blocked.clear();
			// 按候选单元原有顺序重新检查前驱，保持清理顺序稳定。
			for (auto cell : result) {
				if (next.erase(cell))
					blocked.push_back(cell);
				if (next.empty())
					break;
			}
		}
		return result;
	}

	// 检查可编辑性以及每个输出的外部使用者。
	bool can_remove(Cell *cell, const pool<Cell *> &candidates, const pool<Cell *> &replaced_users, const pool<SigBit> &replaced_outputs,
			const pool<SigBit> &retained_inputs)
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
				const auto *info = state->query(bit);
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
	std::shared_ptr<PmuxConnectivity> state;
	using BitInfo = PmuxConnectivity::BitInfo;

	// 索引副本共享同一份连接变化通知和缓存，生命周期由所有使用者共同管理。
	PmuxCoarseIndex(Module *module, std::shared_ptr<PmuxConnectivity> state) : module(module), sigmap(state->sigmap), state(std::move(state)) {}

	// 网表变化后清除旧的驱动和可编辑性查询结果。
	void refresh_caches() const
	{
		if (state->cache_revision == state->revision)
			return;
		state->bit_cache.clear();
		state->editable_cache.clear();
		state->cache_revision = state->revision;
	}

	// 重新收集受保护和双向端口的代表位。
	void refresh_protected_bits() const
	{
		if (!state->protected_wires || state->blacked_out) {
			state->blacked_out = false;
			state->protected_wires.emplace();
			for (auto wire : module->wires())
				if (wire->get_bool_attribute(ID::keep) || (wire->port_input && wire->port_output))
					state->protected_wires->push_back(wire);
		}
		if (!state->aliases_changed)
			return;
		state->kept_bits.clear();
		state->inout_bits.clear();
		for (auto wire : *state->protected_wires) {
			bool keep = wire->get_bool_attribute(ID::keep);
			bool inout = wire->port_input && wire->port_output;
			for (auto bit : sigmap(wire)) {
				if (!bit.wire)
					continue;
				if (keep)
					state->kept_bits.insert(bit);
				if (inout)
					state->inout_bits.insert(bit);
			}
		}
		state->aliases_changed = false;
	}

	// 限定当前选择范围并保留带 keep 属性的单元。
	bool editable_cell(Cell *cell) const { return module->design->selected(module, cell) && !cell->get_bool_attribute(ID::keep); }

	// 确认输出由指定端口独占驱动且允许改写。
	bool editable_output(Cell *cell, IdString name, int offset, SigBit bit)
	{
		auto driver = source(bit);
		if (!driver || driver->cell != cell || driver->port != name || driver->offset != offset)
			return false;
		refresh_protected_bits();
		return !state->kept_bits.count(bit);
	}

	// 汇总端口方向，排除多驱动和双向驱动信号。
	BitInfo bit_info(SigBit bit) const
	{
		if (!bit.wire || bit.wire->module != module)
			return {};
		refresh_caches();
		auto found = state->bit_cache.find(bit);
		if (found != state->bit_cache.end())
			return found->second;
		BitInfo result;
		const auto *info = state->query(bit);
		if (info) {
			if (info->is_input) {
				refresh_protected_bits();
				result.input = !state->inout_bits.count(sigmap(bit));
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
		state->bit_cache.emplace(bit, result);
		return result;
	}

	// 逐位检查指定输出是否允许整体替换。
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

	// 一次搜索内共享访问预算，分别记录已确认的信号和当前路径上的单元。
	struct Traversal {
		pool<SigBit> checked, active_bits;
		pool<Cell *> active, visited;
		int remaining = 65536;
	};

	// 沿组合输入追溯，时序单元仅检查能够异步影响输出的输入端口。
	template <typename Visit> bool visit_cell(Cell *cell, Traversal &walk, Visit visit)
	{
		if (walk.visited.count(cell))
			return true;
		if (!walk.active.insert(cell).second)
			return false;
		for (const auto &[name, signal] : cell->connections()) {
			auto direction = cell->port_dir(name);
			if (direction != RTLIL::PD_INPUT && direction != RTLIL::PD_OUTPUT)
				return false;
			if (direction == RTLIL::PD_OUTPUT || !pmux_combinational_input(cell->type, name))
				continue;
			for (auto input : signal)
				if (!visit(input))
					return false;
		}
		walk.active.erase(cell);
		walk.visited.insert(cell);
		return true;
	}

	// 检查暂存电路中的单元与连线，记录所有来自原模块的数据位。
	bool collect_staged_inputs(const pool<SigBit> &outputs, const Drivers &drivers, pool<SigBit> &inputs)
	{
		Traversal walk;
		for (auto output : outputs)
			if (!visit_staged(output, drivers, inputs, walk, 0))
				return false;
		return true;
	}

	// 跟踪暂存驱动和别名，遇到内部环路时终止搜索。
	bool visit_staged(SigBit bit, const Drivers &drivers, pool<SigBit> &inputs, Traversal &walk, int depth)
	{
		if (bit.wire && bit.wire->module == module)
			bit = sigmap(bit);
		if (!bit.wire || walk.checked.count(bit))
			return true;
		--walk.remaining;
		if (walk.remaining < 0 || depth > 128)
			return false;
		auto visit = [&](SigBit input) { return visit_staged(input, drivers, inputs, walk, depth + 1); };
		auto found = drivers.find(bit);
		if (found == drivers.end()) {
			if (bit.wire->module != module)
				return false;
			inputs.insert(bit);
		} else if (found->second.cell) {
			if (!visit_cell(found->second.cell, walk, visit))
				return false;
		} else {
			if (!walk.active_bits.insert(bit).second || !visit(found->second.alias))
				return false;
			walk.active_bits.erase(bit);
		}
		walk.checked.insert(bit);
		return true;
	}

	// 确认从暂存电路的外部输入沿原模块回溯时不会经过被替换的输出。
	bool comb_independent(const pool<SigBit> &inputs, const pool<SigBit> &targets)
	{
		Traversal walk;
		for (auto input : inputs)
			if (!visit_original(input, targets, walk, 0))
				return false;
		return true;
	}

	// 沿原模块的组合输入回溯并检查目标信号。
	bool visit_original(SigBit bit, const pool<SigBit> &targets, Traversal &walk, int depth)
	{
		if (bit.wire && bit.wire->module == module)
			bit = sigmap(bit);
		if (targets.count(bit))
			return false;
		if (!bit.wire || walk.checked.count(bit))
			return true;
		--walk.remaining;
		if (walk.remaining < 0 || depth > 128)
			return false;
		auto existing = bit_info(bit);
		if (existing.source) {
			auto visit = [&](SigBit input) { return visit_original(input, targets, walk, depth + 1); };
			if (!visit_cell(existing.source->cell, walk, visit))
				return false;
		} else if (!existing.input)
			return false;
		walk.checked.insert(bit);
		return true;
	}
};

// 取出端口或指定分支中仍需保留的数据位，保持偏移顺序。
inline SigSpec pmux_slice(const SigSpec &input, const std::vector<int> &offsets, int base = 0)
{
	SigSpec slice;
	for (int offset : offsets)
		slice.append(input[base + offset]);
	return slice;
}

// 将选择单元的默认输入和其余分支按相同位宽读取。
struct PmuxChoice {
	Cell *cell;
	SigSpec a, b, select, y;

	// 读取选择器的四个端口，检查分支位宽。
	PmuxChoice(PmuxCoarseIndex &index, Cell *cell)
	    : cell(cell), a(index.port(cell, ID::A)), b(index.port(cell, ID::B)), select(index.port(cell, ID::S)), y(index.port(cell, ID::Y))
	{
		log_assert(cell->type == ID($pmux) || (cell->type == ID($mux) && GetSize(select) == 1));
		log_assert(GetSize(a) == width() && GetSize(b) == int64_t{width()} * GetSize(select));
	}

	// 返回每个分支的数据宽度。
	int width() const { return GetSize(y); }
	// 返回包含默认输入在内的分支数量。
	int branches() const { return GetSize(select) + 1; }

	// 分支编号零对应默认输入，正数对应 B 端口内的连续字段。
	SigSpec arm(int branch, int extract_width = -1) const
	{
		int size = extract_width < 0 ? width() : extract_width;
		return branch ? b.extract((branch - 1) * width(), size) : a.extract(0, size);
	}

	// 按分支和偏移读取一个数据位。
	SigBit bit(int branch, int offset) const { return branch ? b[(branch - 1) * width() + offset] : a[offset]; }

	// 按默认分支在前的顺序读取各分支数据。
	std::vector<SigSpec> all_arms(int extract_width = -1) const
	{
		std::vector<SigSpec> result;
		for (int branch = 0; branch < branches(); ++branch)
			result.push_back(arm(branch, extract_width));
		return result;
	}

	// 保留原选择信号，将仍需选择的输出位组合成一个单元。
	void emit_slice(Module &staging, const std::vector<int> &offsets) const
	{
		if (offsets.empty())
			return;
		auto left = pmux_slice(a, offsets);
		auto output = pmux_slice(y, offsets);
		SigSpec right;
		for (int branch = 1; branch < branches(); ++branch)
			right.append(pmux_slice(b, offsets, (branch - 1) * width()));
		auto add = cell->type == ID($mux) ? &Module::addMux : &Module::addPmux;
		(staging.*add)(NEW_ID, left, right, select, output, cell->get_src_attribute());
	}
};

// 已定义分支完全一致时直接复用数据，否则按原分支顺序生成选择器。
inline SigSpec pmux_build_choice(Module *module, const SigSpec &select, const std::vector<SigSpec> &arms, IdString type = ID($mux),
				 IdString *created = nullptr, const std::string &src = {})
{
	const SigSpec *common = nullptr;
	for (const auto &arm : arms) {
		if (arm.is_fully_const() && arm.as_const().is_fully_undef_x_only())
			continue;
		if (common && *common != arm) {
			SigSpec cases;
			for (int i = 1; i < GetSize(arms); ++i)
				cases.append(arms[i]);
			auto name = NEW_ID;
			if (created)
				*created = name;
			if (type == ID($mux) && GetSize(select) == 1)
				return module->Mux(name, arms.front(), cases, select, src);
			return module->Pmux(name, arms.front(), cases, select, src);
		}
		common = &arm;
	}
	return common ? *common : arms.front();
}

YOSYS_NAMESPACE_END

#endif

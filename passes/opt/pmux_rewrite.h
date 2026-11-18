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

// 基础设施层的网表改写工具。在暂存模块中构造候选电路，检查无用单元和组合环路后再提交。

#ifndef YOSYS_PMUX_REWRITE_H
#define YOSYS_PMUX_REWRITE_H

#include "passes/opt/pmux_coarse.h"
#include <algorithm>
#include <optional>

YOSYS_NAMESPACE_BEGIN

// 管理一次候选网表改写及其安全检查。
class PmuxRewrite
{
      public:
	Module staging;
	const pool<Cell *> &removed = removed_cells;

	// 绑定原模块和共享索引，独立构造候选电路。
	PmuxRewrite(Module *module, PmuxCoarseIndex &index, const char *rule) : module(module), index(index), rule(rule)
	{
		log_assert(module == index.module && module->design);
	}
	PmuxRewrite(const PmuxRewrite &) = delete;
	PmuxRewrite &operator=(const PmuxRewrite &) = delete;

	// 根据明确的输入输出边界查找可移除单元。
	void find_removable(const pool<Cell *> &candidates, const pool<Cell *> &replaced_users, const pool<SigBit> &outputs,
			    const pool<SigBit> &inputs)
	{
		log_assert(!validated);
		RemovalBoundary boundary{index.normalize_bits(outputs), index.normalize_bits(inputs), index.revision()};
		removed_cells = index.removable_normalized(candidates, replaced_users, boundary.outputs, boundary.inputs);
		removal_boundary.reset();
		// 只有已删除的使用者才可在最终验证时忽略。
		if (std::all_of(replaced_users.begin(), replaced_users.end(), [&](auto cell) { return removed.count(cell); }))
			removal_boundary.emplace(std::move(boundary));
	}
	// 从暂存电路推导边界并查找可移除单元。
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

	// 在暂存模块中连接替换后的输出。
	void connect(const SigSpec &lhs, const SigSpec &rhs) { staging.connect(lhs, rhs); }
	// 复制原单元的属性、参数和连接，供暂存电路调整端口。
	Cell *clone_cell(IdString name, Cell *origin) { return staging.addCell(name, origin); }

	// 确认必要单元均可删除，并验证暂存连接不会形成组合环路。
	bool prepare(const pool<Cell *> &candidates, const pool<Cell *> &required_removed, const pool<Cell *> &replaced_users = {},
		     const pool<SigBit> &outputs = {})
	{
		auto all = candidates;
		all.insert(required_removed.begin(), required_removed.end());
		find_removable(all, replaced_users, outputs);
		for (auto cell : required_removed)
			if (!removed.count(cell))
				return false;
		return validate();
	}
	// 返回暂存电路新增的单元数。
	int added_count() const { return staging.cells_size(); }

	// 校验删除边界与组合路径，标记可提交的候选。
	bool validate()
	{
		log_assert(!validated);
		validated = check_removal();
		removal_boundary.reset();
		return validated;
	}

	// 将通过检查的单元、连线和选择属性写回原模块。
	void commit()
	{
		log_assert(validated);
		dict<Wire *, Wire *> wires;
		for (auto wire : staging.wires())
			wires.emplace(wire, module->addWire(wire->name, wire));
		auto design = module->design;
		bool inherit_selection = !removed.empty() && !design->selected_whole_module(module->name);
		for (auto cell : removed)
			module->remove(cell);
		for (auto cell : staging.cells()) {
			auto replacement = install_cell(cell, wires);
			if (inherit_selection)
				design->select(module, replacement);
		}
		for (const auto &[lhs, rhs] : staging.connections())
			module->connect(remap(lhs, wires), remap(rhs, wires));
		log_debug("PMUX %s in %s: committed.\n", rule, log_id(module));
	}

      private:
	Module *module;
	PmuxCoarseIndex index;
	const char *rule;
	bool validated = false;
	pool<Cell *> removed_cells;

	// 保存可移除性检查所用的边界与网表版本。
	struct RemovalBoundary {
		pool<SigBit> outputs, inputs;
		size_t revision;
	};
	std::optional<RemovalBoundary> removal_boundary;

	// 将暂存端口逐个接入原模块，使连接索引接收到每个新端口的通知。
	Cell *install_cell(Cell *cell, const dict<Wire *, Wire *> &wires)
	{
		auto replacement = module->addCell(cell->name, cell->type);
		replacement->attributes = cell->attributes;
		replacement->parameters = cell->parameters;
		for (const auto &[name, signal] : cell->connections())
			replacement->setPort(name, remap(signal, wires));
		return replacement;
	}

	// 用提交后的模块连线替换暂存连线，保持原有的位偏移和顺序。
	SigSpec remap(const SigSpec &signal, const dict<Wire *, Wire *> &wires) const
	{
		SigSpec result;
		for (const auto &chunk : signal.chunks()) {
			if (chunk.wire && chunk.wire->module == &staging)
				result.append(SigSpec(wires.at(chunk.wire), chunk.offset, chunk.width));
			else
				result.append(chunk);
		}
		return result;
	}

	// 仅对原模块的信号消除别名。
	SigBit canonical(SigBit bit) const { return bit.wire && bit.wire->module == module ? index.sigmap(bit) : bit; }

	// 每个暂存信号位只能有一个驱动，并记录接回原模块的输出位。
	bool record_driver(SigBit bit, PmuxCoarseIndex::Driver driver, PmuxCoarseIndex::Drivers &drivers, pool<SigBit> &outputs)
	{
		bit = canonical(bit);
		if (!bit.wire)
			return false;
		log_assert(bit.wire->module == module || bit.wire->module == &staging);
		if (!drivers.emplace(bit, driver).second)
			return false;
		if (bit.wire->module == module)
			outputs.insert(bit);
		return true;
	}

	// 收集暂存电路的驱动、替换输出和保留输入。
	bool staged_boundary(pool<SigBit> &outputs, pool<SigBit> &retained, PmuxCoarseIndex::Drivers &drivers)
	{
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
					else if (!record_driver(bit, {cell, SigBit()}, drivers, outputs))
						return false;
				}
			}
		}
		for (const auto &[lhs, rhs] : staging.connections()) {
			for (int i = 0; i < GetSize(lhs); ++i) {
				if (!record_driver(lhs[i], {nullptr, rhs[i]}, drivers, outputs))
					return false;
				retain(rhs[i]);
			}
		}
		for (auto bit : outputs)
			retained.erase(bit);
		return true;
	}

	// 检查旧驱动可被移除且新电路不会引入环路。
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

		bool checked_removal = removal_boundary && removal_boundary->revision == index.revision() && removal_boundary->outputs == outputs &&
				       removal_boundary->inputs == retained;
		if (!checked_removal &&
		    !std::all_of(removed.begin(), removed.end(), [&](Cell *cell) { return index.can_remove(cell, removed, {}, outputs, retained); }))
			return false;
		return index.independent_rewrite(outputs, drivers);
	}
};

YOSYS_NAMESPACE_END

#endif

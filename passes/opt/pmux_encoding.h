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

// 基础设施层的控制信号编码工具。用二值真值表计算已知选择条件，用三态真值表检查控制位未知时的分支。

#ifndef YOSYS_PMUX_ENCODING_H
#define YOSYS_PMUX_ENCODING_H

#include "passes/opt/pmux_coarse.h"

#include <array>
#include <bitset>
#include <cstdint>
#include <ranges>

YOSYS_NAMESPACE_BEGIN

// 用两个掩码分别记录已知为零和已知为一的控制位。
struct PmuxPartialCode {
	unsigned zero, one;
};

enum class BranchKind { Undefined, Selected, Dynamic };

// 表示某行选中的分支及选择不确定时的行为。
struct PmuxBranchChoice {
	BranchKind kind = BranchKind::Undefined;
	int index = 0;
};

// 检查各分支条件互斥并建立二值编码到分支的映射。
inline std::optional<std::vector<int>> pmux_branch_table(const std::vector<uint64_t> &truths, int controls, uint64_t valid_mask = ~uint64_t(0))
{
	int rows = pmux_encoding_limit(controls);
	if (rows != pmux_max_rows)
		valid_mask &= (uint64_t(1) << rows) - 1;
	uint64_t seen = 0;
	std::vector<int> branches(rows);
	for (int i = 0; i < GetSize(truths); ++i) {
		uint64_t active = truths[i] & valid_mask;
		if (seen & active)
			return std::nullopt;
		seen |= active;
		for (int row = 0; row < rows; ++row)
			if (active & (uint64_t(1) << row))
				branches[row] = i + 1;
	}
	return branches;
}

// 在有限控制位上计算选择条件的真值表。
class PmuxEncoding
{
      public:
	// 从指定模块的索引读取控制逻辑。
	explicit PmuxEncoding(PmuxCoarseIndex &index) : index(index) {}
	// 取得按首次出现顺序排列的控制位。
	const std::vector<SigBit> &controls() const { return controls_; }
	// 查询控制信号对应的编码位置。
	const dict<SigBit, int> &slots() const { return slots_; }
	// 取得参与译码的逻辑单元。
	const pool<Cell *> &cells() const { return cells_; }

	// 按信号顺序构造用于选择器分组的键。
	SigSpec control_key() const
	{
		auto sorted = controls_;
		std::sort(sorted.begin(), sorted.end());
		return SigSpec(sorted);
	}

	// 将输入位固定为独立控制变量。
	std::optional<uint64_t> pin(SigBit bit) { return literal(index.sigmap(bit)); }

	// 递归计算控制信号的二值真值表，每个掩码最多表示 64 行。
	std::optional<uint64_t> decode(SigBit bit, int depth = 12)
	{
		bit = index.sigmap(bit);
		if (slots_.count(bit))
			return literal(bit);
		auto found = truths_.find(bit);
		if (found != truths_.end())
			return found->second;
		auto source = index.source(bit);
		if (!source || source->port != ID::Y || GetSize(source->cell->getPort(ID::Y)) != 1)
			return literal(bit);
		auto cell = source->cell;
		if (!cell->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor),
				   ID($reduce_xnor), ID($not), ID($and), ID($or), ID($xor), ID($xnor), ID($logic_and), ID($logic_or), ID($mux)))
			return literal(bit);
		if (depth == 0 || GetSize(cells_) >= 128 || !active.insert(bit).second)
			return std::nullopt;
		auto result =
		  gate<uint64_t>(cell, [&](SigBit input, bool recursive) { return recursive ? decode(input, depth - 1) : literal(input); });
		active.erase(bit);
		if (result) {
			cells_.insert(cell);
			truths_[bit] = *result;
		}
		return result;
	}

	// 使用同一组控制变量计算多个选择器的分支表。
	bool branch_tables(const std::vector<SigSpec> &selects, std::vector<std::vector<int>> &tables)
	{
		decoded_ = false;
		std::vector<std::vector<uint64_t>> truths;
		for (const auto &select : selects) {
			auto &truth = truths.emplace_back();
			for (auto bit : select) {
				auto value = decode(bit);
				if (!value)
					return false;
				truth.push_back(*value);
			}
		}
		tables.clear();
		for (const auto &truth : truths) {
			auto branches = pmux_branch_table(truth, GetSize(controls_));
			if (!branches)
				return false;
			tables.push_back(std::move(*branches));
		}
		decoded_ = true;
		return true;
	}

	// 计算一个选择器在各二值编码下的分支。
	bool branch_table(const SigSpec &select, std::vector<int> &branches)
	{
		std::vector<std::vector<int>> tables;
		if (!branch_tables({select}, tables))
			return false;
		branches = std::move(tables.front());
		return true;
	}

	// 列举包含未知控制位的全部三态编码。
	std::vector<PmuxPartialCode> partial_codes() const
	{
		std::vector<PmuxPartialCode> result(powers_of_three[GetSize(controls_)]);
		for (int slot = 0; slot < GetSize(controls_); ++slot)
			for (int row = 0; row < GetSize(result); ++row) {
				if (ternary_patterns()[slot].zero[row])
					result[row].zero |= 1u << slot;
				if (ternary_patterns()[slot].one[row])
					result[row].one |= 1u << slot;
			}
		return result;
	}

	// 计算每个三态编码下可确定的分支或未知选择。
	std::vector<std::vector<PmuxBranchChoice>> partial_branches(const std::vector<Cell *> &selections) const
	{
		log_assert(decoded_);
		dict<SigBit, TernaryTruth> cache;
		std::vector<std::vector<PmuxBranchChoice>> result;
		int count = powers_of_three[GetSize(controls_)];
		for (auto cell : selections) {
			std::vector<TernaryTruth> predicates;
			for (auto bit : index.port(cell, ID::S)) {
				auto truth = ternary_truth(bit, cache);
				log_assert(truth.has_value());
				predicates.push_back(std::move(*truth));
			}
			auto &choices = result.emplace_back(count);
			for (int row = 0; row < count; ++row) {
				auto &choice = choices[row];
				choice.kind = BranchKind::Selected;
				for (int branch = 0; branch < GetSize(predicates); ++branch) {
					const auto &predicate = predicates[branch];
					if (predicate.zero[row])
						continue;
					if (choice.index || !predicate.one[row]) {
						choice = {cell->type == ID($mux) ? BranchKind::Dynamic : BranchKind::Undefined, 0};
						break;
					}
					choice.index = branch + 1;
				}
			}
		}
		return result;
	}

      private:
	static constexpr std::array<uint64_t, pmux_max_controls> patterns = {
	  0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000,
	};
	static constexpr std::array<int, pmux_max_controls + 1> powers_of_three = {1, 3, 9, 27, 81, 243, 729};
	static constexpr int max_partial_codes = powers_of_three.back();

	// 分别保存结果确定为零、确定为一的编码行。
	struct TernaryTruth {
		using Rows = std::bitset<max_partial_codes>;
		Rows zero = ~Rows(), one;

		// 交换零值行与一值行，保留未知行。
		TernaryTruth operator~() const { return {one, zero}; }
		// 按三态与门规则合并两组编码。
		TernaryTruth operator&(const TernaryTruth &rhs) const { return {zero | rhs.zero, one & rhs.one}; }
		// 按三态或门规则合并两组编码。
		TernaryTruth operator|(const TernaryTruth &rhs) const { return {zero & rhs.zero, one | rhs.one}; }
		// 仅在两个输入均确定时计算异或。
		TernaryTruth operator^(const TernaryTruth &rhs) const
		{
			return {(zero & rhs.zero) | (one & rhs.one), (zero & rhs.one) | (one & rhs.zero)};
		}
	};

	// 按选择位的二值掩码组合两路输入。
	static uint64_t mux_truth(uint64_t a, uint64_t b, uint64_t select) { return (~select & a) | (select & b); }

	// 在选择位未知时保留两路相同的确定值。
	static TernaryTruth mux_truth(const TernaryTruth &a, const TernaryTruth &b, const TernaryTruth &select)
	{
		// 选择信号未知时，两路相同的已知值仍能确定输出。
		return {(select.zero & a.zero) | (select.one & b.zero) | (a.zero & b.zero),
			(select.zero & a.one) | (select.one & b.one) | (a.one & b.one)};
	}

	// 为每个控制位生成三态编码中的零值行和一值行。
	static std::array<TernaryTruth, pmux_max_controls> make_ternary_patterns()
	{
		std::array<TernaryTruth, pmux_max_controls> values;
		for (int slot = 0; slot < pmux_max_controls; ++slot) {
			values[slot].zero.reset();
			for (int row = 0; row < max_partial_codes; ++row) {
				int digit = row / powers_of_three[slot] % 3;
				values[slot].zero[row] = digit == 0;
				values[slot].one[row] = digit == 1;
			}
		}
		return values;
	}

	// 共享所有三态控制变量的基础真值表。
	static const std::array<TernaryTruth, pmux_max_controls> &ternary_patterns()
	{
		static const auto result = make_ternary_patterns();
		return result;
	}

	PmuxCoarseIndex index;
	dict<SigBit, uint64_t> truths_;
	pool<SigBit> active;
	std::vector<SigBit> controls_;
	dict<SigBit, int> slots_;
	pool<Cell *> cells_;
	bool decoded_ = false;

	// 取得常量或独立控制位的二值真值表。
	std::optional<uint64_t> literal(SigBit bit)
	{
		if (!bit.wire) {
			if (bit == State::S0)
				return 0;
			if (bit == State::S1)
				return ~uint64_t(0);
			return std::nullopt;
		}
		if (active.count(bit))
			return std::nullopt;
		auto slot = slots_.find(bit);
		if (slot != slots_.end())
			return patterns[slot->second];
		auto known = truths_.find(bit);
		if (known != truths_.end())
			return known->second;
		if (GetSize(controls_) == pmux_max_controls)
			return std::nullopt;
		slots_[bit] = GetSize(controls_);
		controls_.push_back(bit);
		return patterns[controls_.size() - 1];
	}

	// 对每个编码同时比较两个操作数，累积所有位的相等条件。
	template <typename Truth, typename Read> std::optional<Truth> comparison_truth(Cell *cell, const Read &read) const
	{
		auto operands = pmux_comparison_operands(cell, pmux_max_rows, index.sigmap);
		if (!operands)
			return std::nullopt;
		const auto &[a, b] = *operands;
		Truth equal = ~Truth{};
		for (int i = 0; i < GetSize(a); ++i) {
			auto lhs = read(a[i], GetSize(a) == 1);
			auto rhs = read(b[i], GetSize(a) == 1);
			if (!lhs || !rhs)
				return std::nullopt;
			equal = equal & ~(*lhs ^ *rhs);
		}
		return cell->type == ID($ne) ? ~equal : equal;
	}

	// 归约端口的各个输入位，或直接读取单比特输入。
	template <typename Truth, typename Read>
	std::optional<Truth> operand_truth(Cell *cell, IdString port, IdString reduction, const Read &read) const
	{
		auto inputs = index.port(cell, port);
		if (reduction.empty())
			return GetSize(inputs) == 1 ? read(inputs[0], true) : std::nullopt;
		if (GetSize(inputs) > pmux_max_rows)
			return std::nullopt;
		bool is_and = reduction == ID($reduce_and);
		bool is_xor = reduction.in(ID($reduce_xor), ID($reduce_xnor));
		Truth result = is_and ? ~Truth{} : Truth{};
		for (auto bit : inputs) {
			auto input = read(bit, true);
			if (!input)
				return std::nullopt;
			if (is_and)
				result = result & *input;
			else if (is_xor)
				result = result ^ *input;
			else
				result = result | *input;
		}
		return reduction == ID($reduce_xnor) ? ~result : result;
	}

	// 使用相同门语义计算二值编码和包含未知控制位的三态编码。
	template <typename Truth, typename Read> std::optional<Truth> gate(Cell *cell, const Read &read) const
	{
		auto type = cell->type;
		if (type.in(ID($eq), ID($ne), ID($logic_not)))
			return comparison_truth<Truth>(cell, read);
		auto operand = [&](IdString port, IdString reduction = {}) { return operand_truth<Truth>(cell, port, reduction, read); };
		if (type.in(ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor)))
			return operand(ID::A, type);
		IdString reduction = type.in(ID($logic_and), ID($logic_or)) ? ID($reduce_or) : IdString();
		auto lhs = operand(ID::A, reduction);
		if (!lhs)
			return std::nullopt;
		if (type == ID($not))
			return ~*lhs;
		auto rhs = operand(ID::B, reduction);
		if (!rhs)
			return std::nullopt;
		if (type == ID($mux)) {
			auto select = operand(ID::S);
			return select ? std::optional<Truth>{mux_truth(*lhs, *rhs, *select)} : std::nullopt;
		}
		if (type.in(ID($and), ID($logic_and)))
			return *lhs & *rhs;
		if (type.in(ID($or), ID($logic_or)))
			return *lhs | *rhs;
		log_assert(type.in(ID($xor), ID($xnor)));
		auto parity = *lhs ^ *rhs;
		return type == ID($xnor) ? ~parity : parity;
	}

	// 按三态门语义递归计算并缓存选择信号。
	std::optional<TernaryTruth> ternary_truth(SigBit bit, dict<SigBit, TernaryTruth> &cache) const
	{
		auto slot = slots_.find(bit);
		if (slot != slots_.end())
			return ternary_patterns()[slot->second];
		if (!bit.wire) {
			if (bit == State::S0)
				return TernaryTruth{};
			if (bit == State::S1)
				return ~TernaryTruth{};
			return TernaryTruth{{}, {}};
		}
		auto found = cache.find(bit);
		if (found != cache.end())
			return found->second;
		if (!truths_.count(bit))
			return std::nullopt;
		auto source = index.source(bit);
		log_assert(source.has_value());
		auto result = gate<TernaryTruth>(source->cell, [&](SigBit input, bool) { return ternary_truth(input, cache); });
		if (result)
			cache[bit] = *result;
		return result;
	}
};

// 为选择器记录每个编码行选中的分支。
struct PmuxEncodedChoice : PmuxChoice {
	using PmuxChoice::PmuxChoice;
	std::vector<int> rows;

	// 读取给定编码行中的指定数据位。
	SigBit encoded_data(int code, int offset) const { return bit(rows[code], offset); }

	// 按编码行顺序对选中的分支执行同一计算。
	template <typename Fn> auto map_rows(Fn fn) const
	{
		return std::views::iota(0, GetSize(rows)) | std::views::transform([this, fn](int row) { return fn(row, rows[row]); });
	}
};

// 记录含未知控制位的编码；需要验证某个分支时再计算选择结果。
struct PmuxPartialTable {
	std::vector<PmuxPartialCode> codes;
	unsigned row_count;
	std::vector<Cell *> cells;
	std::optional<std::vector<std::vector<PmuxBranchChoice>>> branches;

	// 首次查询时计算组内各选择器的三态分支表。
	const auto &choices(const PmuxEncoding &encoding)
	{
		log_assert(!cells.empty());
		if (!branches)
			branches = encoding.partial_branches(cells);
		return *branches;
	}

	// 记录每行的已知控制位和完整编码总数。
	explicit PmuxPartialTable(const PmuxEncoding &encoding)
	    : codes(encoding.partial_codes()), row_count(pmux_encoding_limit(GetSize(encoding.controls())))
	{
	}

	// 返回给定编码行中仍未确定的控制位。
	unsigned unknown(int row) const { return (row_count - 1) & ~(codes[row].one | codes[row].zero); }

	// 每个掩码标出与当前三态编码相容的全部二值编码。
	std::vector<uint64_t> completions() const
	{
		std::vector<uint64_t> result(codes.size());
		for (int row = 0; row < GetSize(codes); ++row) {
			const auto &[zero, one] = codes[row];
			for (unsigned code = one; code < row_count; ++code)
				if ((code & (zero | one)) == one)
					result[row] |= uint64_t(1) << code;
		}
		return result;
	}
};

// 检查选择器端口形状以及分支数和表规模上限。
inline bool pmux_select_shape(Cell *cell)
{
	if (!cell->type.in(ID($mux), ID($pmux)))
		return false;
	int width = GetSize(cell->getPort(ID::Y));
	int branches = GetSize(cell->getPort(ID::S));
	return width > 0 && width <= pmux_max_table_bits && branches > 0 && branches <= pmux_max_rows && GetSize(cell->getPort(ID::A)) == width &&
	       GetSize(cell->getPort(ID::B)) == width * branches && (cell->type == ID($pmux) || branches == 1);
}

YOSYS_NAMESPACE_END

#endif

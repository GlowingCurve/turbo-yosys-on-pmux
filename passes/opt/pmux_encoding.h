#ifndef YOSYS_PMUX_ENCODING_H
#define YOSYS_PMUX_ENCODING_H

#include "passes/opt/pmux_coarse.h"

#include <array>
#include <bitset>
#include <cstdint>

YOSYS_NAMESPACE_BEGIN

inline constexpr int pmux_max_controls = 6;
inline constexpr int pmux_max_rows = 1 << pmux_max_controls;
inline constexpr int pmux_max_table_bits = 32768;

struct PmuxPartialCode
{
	unsigned zero, one;
};

struct PmuxBranchChoice
{
	// -1 是默认分支，-2 表示无确定的选择结果。
	int first = -2, second = -2;
};

class PmuxEncoding
{
	static constexpr std::array<uint64_t, pmux_max_controls> patterns = {
		0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
		0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000,
	};
	static constexpr std::array<int, pmux_max_controls + 1> powers_of_three = {1, 3, 9, 27, 81, 243, 729};
	static constexpr int max_partial_codes = powers_of_three.back();

	struct TernaryTruth {
		using Rows = std::bitset<max_partial_codes>;
		Rows zero = ~Rows(), one;

		TernaryTruth operator~() const { return {one, zero}; }
		TernaryTruth operator&(const TernaryTruth &rhs) const { return {zero | rhs.zero, one & rhs.one}; }
		TernaryTruth operator|(const TernaryTruth &rhs) const { return {zero & rhs.zero, one | rhs.one}; }
		TernaryTruth operator^(const TernaryTruth &rhs) const
		{
			return {(zero & rhs.zero) | (one & rhs.one), (zero & rhs.one) | (one & rhs.zero)};
		}
	};

	static uint64_t mux_truth(uint64_t a, uint64_t b, uint64_t select)
	{
		return (~select & a) | (select & b);
	}

	static TernaryTruth mux_truth(const TernaryTruth &a, const TernaryTruth &b, const TernaryTruth &select)
	{
		// 选择信号未知时，两路相同的已知值仍能确定输出。
		return {(select.zero & a.zero) | (select.one & b.zero) | (a.zero & b.zero),
			(select.zero & a.one) | (select.one & b.one) | (a.one & b.one)};
	}

	static const std::array<TernaryTruth, pmux_max_controls> &ternary_patterns()
	{
		static const auto result = [] {
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
		}();
		return result;
	}

	const PmuxCoarseIndex &index;
	dict<SigBit, uint64_t> decoded;
	pool<SigBit> active;

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
		auto slot = slots.find(bit);
		if (slot != slots.end())
			return patterns[slot->second];
		auto known = decoded.find(bit);
		if (known != decoded.end())
			return known->second;
		if (GetSize(controls) == pmux_max_controls)
			return std::nullopt;
		int position = GetSize(controls);
		controls.push_back(bit);
		slots[bit] = position;
		return patterns[position];
	}

	template<typename Truth, typename Read>
	std::optional<Truth> comparison(Cell *cell, const Read &read) const
	{
		auto operands = index.comparison_operands(cell, pmux_max_rows);
		if (!operands)
			return std::nullopt;
		const auto &[a, b] = *operands;

		Truth equal = ~Truth{};
		for (int i = 0; i < GetSize(a); ++i) {
			auto lhs = read(a[i], GetSize(a) == 1);
			auto rhs = read(b[i], GetSize(b) == 1);
			if (!lhs || !rhs)
				return std::nullopt;
			equal = equal & ~(*lhs ^ *rhs);
		}
		return cell->type == ID($ne) ? ~equal : equal;
	}

	template<typename Truth, typename Read>
	std::optional<Truth> gate(Cell *cell, const Read &read) const
	{
		if (cell->type.in(ID($eq), ID($ne), ID($logic_not)))
			return comparison<Truth>(cell, read);
		auto a = index.port(cell, ID::A);
		auto reduce = [&](const SigSpec &inputs, IdString type) -> std::optional<Truth> {
			if (GetSize(inputs) > pmux_max_rows)
				return std::nullopt;
			bool is_and = type == ID($reduce_and);
			bool is_xor = type.in(ID($reduce_xor), ID($reduce_xnor));
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
			return type == ID($reduce_xnor) ? ~result : result;
		};
		if (cell->type.in(ID($reduce_or), ID($reduce_bool), ID($reduce_and), ID($reduce_xor), ID($reduce_xnor)))
			return reduce(a, cell->type);
		if (cell->type.in(ID($logic_and), ID($logic_or))) {
			auto lhs = reduce(a, ID($reduce_or));
			if (!lhs)
				return std::nullopt;
			auto rhs = reduce(index.port(cell, ID::B), ID($reduce_or));
			if (!rhs)
				return std::nullopt;
			return cell->type == ID($logic_and) ? *lhs & *rhs : *lhs | *rhs;
		}
		if (GetSize(a) != 1)
			return std::nullopt;
		auto lhs = read(a[0], true);
		if (!lhs)
			return std::nullopt;
		if (cell->type == ID($not))
			return ~*lhs;
		auto b = index.port(cell, ID::B);
		if (GetSize(b) != 1)
			return std::nullopt;
		auto rhs = read(b[0], true);
		if (!rhs)
			return std::nullopt;
		if (cell->type == ID($mux)) {
			auto s = index.port(cell, ID::S);
			if (GetSize(s) != 1)
				return std::nullopt;
			auto select = read(s[0], true);
			if (!select)
				return std::nullopt;
			return mux_truth(*lhs, *rhs, *select);
		}
		if (cell->type == ID($and))
			return *lhs & *rhs;
		if (cell->type == ID($or))
			return *lhs | *rhs;
		return cell->type == ID($xnor) ? ~(*lhs ^ *rhs) : *lhs ^ *rhs;
	}

	std::optional<TernaryTruth> ternary_truth(SigBit bit, dict<SigBit, TernaryTruth> &cache) const
	{
		auto slot = slots.find(bit);
		if (slot != slots.end())
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
		if (!decoded.count(bit))
			return std::nullopt;
		auto source = index.source(bit);
		log_assert(source.has_value());
		auto result = gate<TernaryTruth>(source->cell, [&](SigBit input, bool) {
			return ternary_truth(input, cache);
		});
		if (result)
			cache[bit] = *result;
		return result;
	}

public:
	std::vector<SigBit> controls;
	dict<SigBit, int> slots;
	pool<Cell *> cells;

	explicit PmuxEncoding(const PmuxCoarseIndex &index) : index(index) {}

	std::optional<uint64_t> pin(SigBit bit) { return literal(index.sigmap(bit)); }

	std::optional<uint64_t> decode(SigBit bit, int depth = 12)
	{
		bit = index.sigmap(bit);
		if (slots.count(bit))
			return literal(bit);
		auto found = decoded.find(bit);
		if (found != decoded.end())
			return found->second;
		auto source = index.source(bit);
		if (!source || source->port != ID::Y || GetSize(source->cell->getPort(ID::Y)) != 1)
			return literal(bit);
		auto cell = source->cell;
		if (!cell->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_or), ID($reduce_bool), ID($reduce_and),
				ID($reduce_xor), ID($reduce_xnor), ID($not), ID($and), ID($or), ID($xor), ID($xnor),
				ID($logic_and), ID($logic_or), ID($mux)))
			return literal(bit);
		if (depth == 0 || GetSize(cells) >= 128 || !active.insert(bit).second)
			return std::nullopt;
		auto result = gate<uint64_t>(cell, [&](SigBit input, bool recursive) {
			return recursive ? decode(input, depth - 1) : literal(input);
		});
		active.erase(bit);
		if (result) {
			cells.insert(cell);
			decoded[bit] = *result;
		}
		return result;
	}

	bool branch_tables(const std::vector<SigSpec> &selects, std::vector<std::vector<int>> &tables)
	{
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
		int rows = 1 << GetSize(controls);
		uint64_t valid_rows = rows == pmux_max_rows ? ~uint64_t(0) : (uint64_t(1) << rows) - 1;
		tables.clear();
		for (const auto &truth : truths) {
			uint64_t seen = 0;
			auto &branches = tables.emplace_back(rows, -1);
			for (int i = 0; i < GetSize(truth); ++i) {
				uint64_t active_rows = truth[i] & valid_rows;
				if (seen & active_rows)
					return false;
				seen |= active_rows;
				for (int code = 0; code < rows; ++code)
					if (active_rows & (uint64_t(1) << code))
						branches[code] = i;
			}
		}
		return true;
	}

	bool branch_table(const SigSpec &select, std::vector<int> &branches)
	{
		std::vector<std::vector<int>> tables;
		if (!branch_tables({select}, tables))
			return false;
		branches = std::move(tables.front());
		return true;
	}

	std::vector<PmuxPartialCode> partial_codes() const
	{
		std::vector<PmuxPartialCode> result(powers_of_three[GetSize(controls)]);
		for (int slot = 0; slot < GetSize(controls); ++slot)
			for (int row = 0; row < GetSize(result); ++row) {
				if (ternary_patterns()[slot].zero[row])
					result[row].zero |= 1u << slot;
				if (ternary_patterns()[slot].one[row])
					result[row].one |= 1u << slot;
			}
		return result;
	}

	std::vector<std::vector<PmuxBranchChoice>> partial_branches(const std::vector<Cell *> &selections) const
	{
		dict<SigBit, TernaryTruth> cache;
		std::vector<std::vector<PmuxBranchChoice>> result;
		int count = powers_of_three[GetSize(controls)];
		for (auto cell : selections) {
			std::vector<TernaryTruth> predicates;
			for (auto bit : index.port(cell, ID::S)) {
				auto truth = ternary_truth(bit, cache);
				if (!truth)
					return {};
				predicates.push_back(std::move(*truth));
			}
			auto &choices = result.emplace_back(count);
			for (int row = 0; row < count; ++row) {
				int selected = -1;
				bool undefined = false;
				for (int branch = 0; branch < GetSize(predicates); ++branch) {
					const auto &predicate = predicates[branch];
					if (predicate.zero[row])
						continue;
					if (selected >= 0 || !predicate.one[row]) {
						undefined = true;
						break;
					}
					selected = branch;
				}
				if (!undefined)
					choices[row].first = selected;
				else if (cell->type == ID($mux))
					choices[row] = {-1, 0};
			}
		}
		return result;
	}
};

inline bool pmux_select_shape(Cell *cell)
{
	if (!cell->type.in(ID($mux), ID($pmux)))
		return false;
	int width = GetSize(cell->getPort(ID::Y));
	int branches = GetSize(cell->getPort(ID::S));
	return width > 0 && width <= pmux_max_table_bits && branches > 0 && branches <= pmux_max_rows &&
		GetSize(cell->getPort(ID::A)) == width && GetSize(cell->getPort(ID::B)) == width * branches &&
		(cell->type == ID($pmux) || branches == 1);
}

inline SigSpec pmux_control_key(const PmuxEncoding &encoding)
{
	auto sorted = encoding.controls;
	std::sort(sorted.begin(), sorted.end());
	return SigSpec(sorted);
}

YOSYS_NAMESPACE_END

#endif

#ifndef YOSYS_PMUX_ENCODING_H
#define YOSYS_PMUX_ENCODING_H

#include "passes/opt/pmux_coarse.h"

#include <array>
#include <bitset>
#include <cstdint>

YOSYS_NAMESPACE_BEGIN

struct PmuxPartialCode
{
	unsigned zero, one;
};

enum class BranchKind { Constant, Selected, Dynamic };

struct PmuxBranchChoice {
	BranchKind kind = BranchKind::Constant;
	int index = 0;
	State val = State::Sx;
};

inline std::optional<std::vector<int>> pmux_branch_table(const std::vector<uint64_t> &truths, int controls,
		uint64_t valid_mask = ~uint64_t(0))
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

	PmuxCoarseIndex &index;
	dict<SigBit, uint64_t> truths_;
	pool<SigBit> active;
	std::vector<SigBit> controls_;
	dict<SigBit, int> slots_;
	pool<Cell *> cells_;
	bool decoded_ = false;

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

	template<typename Truth, typename Read>
	std::optional<Truth> gate(Cell *cell, const Read &read) const
	{
		auto type = cell->type;
		if (type.in(ID($eq), ID($ne), ID($logic_not))) {
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
			return type == ID($ne) ? ~equal : equal;
		}
		auto operand = [&](IdString port, IdString reduction = {}) -> std::optional<Truth> {
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
				result = is_and ? result & *input : is_xor ? result ^ *input : result | *input;
			}
			return reduction == ID($reduce_xnor) ? ~result : result;
		};
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
		auto result = gate<TernaryTruth>(source->cell, [&](SigBit input, bool) {
			return ternary_truth(input, cache);
		});
		if (result)
			cache[bit] = *result;
		return result;
	}

public:
	explicit PmuxEncoding(PmuxCoarseIndex &index) : index(index) {}
	const std::vector<SigBit> &controls() const { return controls_; }
	const dict<SigBit, int> &slots() const { return slots_; }
	const pool<Cell *> &cells() const { return cells_; }

	SigSpec control_key() const
	{
		auto sorted = controls_;
		std::sort(sorted.begin(), sorted.end());
		return SigSpec(sorted);
	}

	std::optional<uint64_t> pin(SigBit bit) { return literal(index.sigmap(bit)); }

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
		if (!cell->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_or), ID($reduce_bool), ID($reduce_and),
				ID($reduce_xor), ID($reduce_xnor), ID($not), ID($and), ID($or), ID($xor), ID($xnor),
				ID($logic_and), ID($logic_or), ID($mux)))
			return literal(bit);
		if (depth == 0 || GetSize(cells_) >= 128 || !active.insert(bit).second)
			return std::nullopt;
		auto result = gate<uint64_t>(cell, [&](SigBit input, bool recursive) {
			return recursive ? decode(input, depth - 1) : literal(input);
		});
		active.erase(bit);
		if (result) {
			cells_.insert(cell);
			truths_[bit] = *result;
		}
		return result;
	}

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
						choice = {cell->type == ID($mux) ? BranchKind::Dynamic : BranchKind::Constant, 0, State::Sx};
						break;
					}
					choice.index = branch + 1;
				}
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

YOSYS_NAMESPACE_END

#endif

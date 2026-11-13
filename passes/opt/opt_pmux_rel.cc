#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

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
	std::vector<Parity> rows, branches;
	int selection = 0;
	int term_count = 0;
	int inversions = 0;
	int reference = -1;
	Parity delta;
};

struct Selection {
	Cell *cell;
	std::vector<Column> columns;
	pool<Cell *> producers;
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

	static Parity condition(Parity value, PmuxPartialCode code, const PmuxEncoding &encoding)
	{
		auto kept = std::remove_if(value.terms.begin(), value.terms.end(), [&](SigBit bit) {
			auto slot = encoding.slots.find(bit);
			if (slot == encoding.slots.end())
				return false;
			unsigned mask = 1u << slot->second;
			value.inverted ^= (code.one & mask) != 0;
			value.undef |= ((code.one | code.zero) & mask) == 0;
			return true;
		});
		value.terms.erase(kept, value.terms.end());
		return value;
	}

	bool partial_relation(const Column &base, const Column &other, const Parity &delta, const PmuxEncoding &encoding,
			const std::vector<PmuxPartialCode> &codes, const std::vector<std::vector<PmuxBranchChoice>> &choices) const
	{
		if (choices.empty())
			return false;
		unsigned full_mask = (1u << GetSize(encoding.controls)) - 1;
		for (int row = 0; row < GetSize(codes); ++row) {
			auto code = codes[row];
			if ((code.one | code.zero) == full_mask)
				continue;
			auto target = choices[other.selection][row];
			if (target.first == -2)
				continue;
			Parity target_a = condition(other.branches[target.first + 1], code, encoding), target_b;
			if (target.second != -2)
				target_b = condition(other.branches[target.second + 1], code, encoding);
			// 单个 mux 的选择位未知时，任一分支未知都会使结果未知。
			if (target_a.undef || target_b.undef)
				continue;
			auto source = choices[base.selection][row];
			if (source.first == -2)
				return false;
			auto matches = [&](int branch) {
				if (branch == -2)
					return true;
				Parity value = condition(base.branches[branch + 1], code, encoding);
				auto matches_target = [&](const Parity &expected) {
					return difference(value, expected) == delta &&
						std::includes(expected.terms.begin(), expected.terms.end(), value.terms.begin(), value.terms.end()) &&
						std::includes(expected.terms.begin(), expected.terms.end(), delta.terms.begin(), delta.terms.end());
				};
				return matches_target(target_a) || (target.second != -2 && matches_target(target_b));
			};
			if (!matches(source.first) || !matches(source.second))
				return false;
		}
		return true;
	}

	std::unique_ptr<PmuxRewrite> relations(const std::vector<Cell *> &cells, const PmuxEncoding *encoding = nullptr,
			const std::vector<std::vector<int>> &tables = {})
	{
		operators.clear();
		std::vector<Selection> selections;
		selections.reserve(cells.size());
		std::vector<Column *> columns;
		pool<Cell *> candidates, replaced;
		int inspected = 0;
		for (int i = 0; i < GetSize(cells); ++i) {
			auto cell = cells[i];
			int branches = GetSize(cell->getPort(ID::S)) + 1;
			int rows = encoding ? GetSize(tables[i]) : branches;
			SigSpec a = index.port(cell, ID::A), b = index.port(cell, ID::B), y = index.port(cell, ID::Y);
			int width = GetSize(y);
			if (width > 4096)
				continue;
			inspected += std::max(rows, branches) * width;
			if (inspected > 65536)
				break;
			auto &selection = selections.emplace_back(Selection{cell, {}, {}});
			for (int offset = 0; offset < width; ++offset) {
				auto &column = selection.columns.emplace_back();
				column.output = y[offset];
				column.selection = GetSize(selections) - 1;
				for (int branch = -1; branch < branches - 1; ++branch) {
					auto value = expression(branch < 0 ? a[offset] : b[branch * width + offset], selection.producers);
					if (!value)
						break;
					column.branches.push_back(std::move(*value));
				}
				if (GetSize(column.branches) != branches)
					continue;
				for (int row = 0; row < rows; ++row) {
					int branch = encoding ? tables[i][row] : row - 1;
					Parity value = column.branches[branch + 1];
					if (encoding) {
						unsigned mask = (1u << GetSize(encoding->controls)) - 1;
						value = condition(std::move(value), {mask ^ unsigned(row), unsigned(row)}, *encoding);
					}
					column.term_count += GetSize(value.terms);
					column.inversions += value.inverted;
					column.rows.push_back(std::move(value));
				}
			}
			for (auto &column : selection.columns)
				columns.push_back(&column);
		}
		std::stable_sort(columns.begin(), columns.end(), [](const Column *a, const Column *b) {
			return std::tie(a->term_count, a->inversions) < std::tie(b->term_count, b->inversions);
		});
		dict<std::vector<Parity>, std::vector<int>> groups;
		std::vector<PmuxPartialCode> partial_codes;
		std::vector<std::vector<PmuxBranchChoice>> choices;
		bool partial_prepared = false;
		auto partial_match = [&](const Column &base, const Column &target, const Parity &delta) {
			if (!encoding)
				return true;
			if (!partial_prepared) {
				std::vector<Cell *> selected;
				for (const auto &selection : selections)
					selected.push_back(selection.cell);
				partial_codes = encoding->partial_codes();
				choices = encoding->partial_branches(selected);
				partial_prepared = true;
			}
			return partial_relation(base, target, delta, *encoding, partial_codes, choices);
		};
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
				if (usable_relation(*columns[base], column, delta) && partial_match(*columns[base], column, delta)) {
					column.reference = base;
					column.delta = std::move(delta);
					break;
				}
			}
			if (column.reference == -1 && GetSize(bases) < 32)
				bases.push_back(col);
		}
		struct MuxPlan {
			Cell *cell;
			SigSpec a, b, y;
		};
		std::vector<MuxPlan> muxes;
		pool<SigBit> inputs, outputs;
		for (const auto &selection : selections) {
			if (std::none_of(selection.columns.begin(), selection.columns.end(), [](const Column &col) { return col.reference >= 0; }))
				continue;
			auto cell = selection.cell;
			candidates.insert(cell);
			candidates.insert(selection.producers.begin(), selection.producers.end());
			replaced.insert(cell);
			SigSpec a = index.port(cell, ID::A), b = index.port(cell, ID::B);
			int width = GetSize(selection.columns);
			std::vector<int> kept;
			MuxPlan plan{cell, {}, {}, {}};
			for (int offset = 0; offset < width; ++offset) {
				const auto &column = selection.columns[offset];
				outputs.insert(column.output);
				if (column.reference < 0) {
					kept.push_back(offset);
					plan.a.append(a[offset]);
					plan.y.append(column.output);
				}
			}
			auto control = index.port(cell, ID::S);
			for (int row = 0; row < GetSize(control); ++row)
				for (int offset : kept)
					plan.b.append(b[row * width + offset]);
			if (!plan.y.empty()) {
				inputs.insert(plan.a.begin(), plan.a.end());
				inputs.insert(plan.b.begin(), plan.b.end());
				inputs.insert(control.begin(), control.end());
				muxes.push_back(std::move(plan));
			}
		}
		if (replaced.empty())
			return nullptr;
		if (encoding)
			candidates.insert(encoding->cells.begin(), encoding->cells.end());
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
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, encoding ? "encoded_output_relation" : "output_relation");
		rewrite->removed = index.removable(candidates, replaced, outputs, inputs);
		for (auto cell : replaced)
			if (!rewrite->removed.count(cell))
				return nullptr;
		auto &staging = rewrite->staging;
		for (const auto &mux : muxes) {
			auto control = index.port(mux.cell, ID::S);
			if (mux.cell->type == ID($mux))
				staging.addMux(NEW_ID, mux.a, mux.b, control, mux.y, mux.cell->get_src_attribute());
			else
				staging.addPmux(NEW_ID, mux.a, mux.b, control, mux.y, mux.cell->get_src_attribute());
		}
		for (const auto &[form, relation] : relations) {
			const auto &[terms, inverted] = form;
			SigSpec left = relation.operands[0];
			if (!terms) {
				if (inverted)
					staging.addNot(NEW_ID, left, relation.y);
				else
					rewrite->connect(relation.y, left);
			}
			for (int term = 1; term <= terms; ++term) {
				bool final = term == terms;
				SigSpec right = relation.operands[term];
				SigSpec output = final ? relation.y : SigSpec(staging.addWire(NEW_ID, GetSize(relation.y)));
				if (final && inverted)
					staging.addXnor(NEW_ID, left, right, output);
				else
					staging.addXor(NEW_ID, left, right, output);
				left = output;
			}
		}
		if (!rewrite->validate())
			return nullptr;
		return rewrite;
	}

	struct SwapColumn {
		int cell, offset;
		std::vector<int> values;
		std::vector<int> branch_values;
	};

	struct SwapPair {
		int first, second, exception;
	};

	struct SwapPartialCodes {
		const PmuxEncoding &encoding;
		std::vector<Cell *> cells;
		std::vector<PmuxPartialCode> codes;
		std::optional<std::vector<std::vector<PmuxBranchChoice>>> branches;
	};

	static bool preserves_partial_swap(const SwapColumn &column, const SwapColumn &other,
			const std::vector<PmuxBranchChoice> &choices, const std::vector<int> &affected, int low, int high)
	{
		for (int row : affected) {
			const auto choice = choices[row];
			if (choice.first == -2)
				continue;
			// 交换位未知时，局部修正和外层交换可能选中对方在例外编码的数据。
			auto preserves = [&](int value) {
				return value == column.branch_values[choice.first + 1] ||
					(choice.second != -2 && value == column.branch_values[choice.second + 1]);
			};
			if (!preserves(other.values[low]) || !preserves(other.values[high]))
				return false;
		}
		return true;
	}

	static std::vector<SwapPair> swap_pairs(const std::vector<SwapColumn> &columns, int mask, SwapPartialCodes *partial)
	{
		int rows = GetSize(columns.front().values);
		std::vector<SwapPair> pairs;
		pool<int> used;
		int budget = pmux_max_table_bits;
		for (int low = partial ? 0 : -1; low < (partial ? rows : 0); ++low) {
			if (low >= 0 && (low & mask))
				continue;
			int high = low | mask;
			std::vector<int> affected;
			if (partial)
				for (int row = 0; row < GetSize(partial->codes); ++row) {
					const auto &code = partial->codes[row];
					unsigned fixed = code.zero | code.one;
					if (!(fixed & mask) && (unsigned(low) & fixed) == code.one)
						affected.push_back(row);
				}
			auto key = [&](const SwapColumn &column, int flip) {
				std::vector<int> result;
				result.reserve(rows);
				for (int row = 0; row < rows; ++row)
					if (row != low && row != high)
						result.push_back(column.values[row ^ flip]);
				return result;
			};
			dict<std::vector<int>, std::vector<int>> groups;
			for (int col = 0; col < GetSize(columns); ++col)
				if (!used.count(col))
					groups[key(columns[col], 0)].push_back(col);
			for (int col = 0; col < GetSize(columns); ++col) {
				if (used.count(col))
					continue;
				const auto &a = columns[col];
				auto partners = groups.find(key(a, mask));
				if (partners == groups.end() || (!partial && std::binary_search(partners->second.begin(), partners->second.end(), col)))
					continue;
				for (int partner : partners->second) {
					if (partner == col || used.count(partner))
					continue;
					const auto &b = columns[partner];
					if (partial) {
						if ((budget -= 1 + GetSize(affected)) < 0)
							return pairs;
						if (a.values[low] == b.values[high] && a.values[high] == b.values[low])
							continue;
						if (!partial->branches)
							partial->branches = partial->encoding.partial_branches(partial->cells);
						const auto &branches = *partial->branches;
						if (branches.empty())
							return pairs;
						if (!preserves_partial_swap(a, b, branches[a.cell], affected, low, high) ||
								!preserves_partial_swap(b, a, branches[b.cell], affected, low, high))
						continue;
				}
					used.insert(col);
					used.insert(partner);
					pairs.push_back({col, partner, low});
					break;
			}
			}
		}
		return pairs;
	}

	std::unique_ptr<PmuxRewrite> swap_outputs(const std::vector<Cell *> &cells, const PmuxEncoding &encoding,
			PmuxSelectTree &tree, const std::vector<SwapColumn> &columns, int flip, SwapPartialCodes *partial = nullptr)
	{
		pool<Cell *> replaced;
		std::vector<int> controls, natural_order, roots, reference;
		std::vector<pool<int>> offsets(cells.size());
		pool<SigBit> inputs, outputs;
		SigSpec swap_y;
		bool shares_selection = false;
		if (partial)
			controls.push_back(flip);
		for (int control = 0; control < GetSize(encoding.controls); ++control) {
			natural_order.push_back(control);
			if (control != flip)
				controls.push_back(control);
		}
		int mask = 1 << flip;
		for (const auto &pair : swap_pairs(columns, mask, partial)) {
			const auto &a = columns[pair.first];
			const auto &b = columns[pair.second];
			std::vector<int> low_a, low_b;
			for (int row = 0; row < GetSize(a.values); ++row) {
				if (row & mask)
					continue;
				low_a.push_back(a.values[row]);
				low_b.push_back(b.values[row]);
				if (partial) {
					low_a.push_back(row == pair.exception ? b.values[row | mask] : a.values[row]);
					low_b.push_back(row == pair.exception ? a.values[row | mask] : b.values[row]);
				}
			}
			shares_selection |= std::adjacent_find(low_a.begin(), low_a.end(), std::not_equal_to<int>{}) != low_a.end() ||
					std::adjacent_find(low_b.begin(), low_b.end(), std::not_equal_to<int>{}) != low_b.end();
			int left = tree.column(std::move(low_a), controls);
			int right = tree.column(std::move(low_b), controls);
			int level = GetSize(controls);
			roots.push_back(tree.select(flip, level, left, right));
			roots.push_back(tree.select(flip, level, right, left));
			for (auto column : {&a, &b}) {
				if (partial)
					reference.push_back(tree.column(column->values, natural_order));
				auto cell = cells[column->cell];
				swap_y.append(index.port(cell, ID::Y)[column->offset]);
				replaced.insert(cell);
				offsets[column->cell].insert(column->offset);
			}
		}
		if (roots.empty() || (partial && tree.mux_bits(roots) >= tree.mux_bits(reference)))
			return nullptr;
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, "encoded_output_swap");
		inputs = tree.inputs(roots);
		auto &staging = rewrite->staging;
		rewrite->connect(swap_y, tree.emit(&staging, roots, cells.front()->get_src_attribute()));
		bool combines_selections = GetSize(replaced) > 1;
		for (int pos = 0; pos < GetSize(cells); ++pos) {
			if (offsets[pos].empty())
				continue;
			auto cell = cells[pos];
			auto a = index.port(cell, ID::A), b = index.port(cell, ID::B), y = index.port(cell, ID::Y), select = index.port(cell, ID::S);
			outputs.insert(y.begin(), y.end());
			SigSpec keep_a, keep_b, keep_y;
			for (int offset = 0; offset < GetSize(y); ++offset)
				if (!offsets[pos].count(offset)) {
					keep_a.append(a[offset]);
					keep_y.append(y[offset]);
				}
			if (keep_y.empty())
				continue;
			combines_selections = false;
			for (int branch = 0; branch < GetSize(select); ++branch)
				for (int offset = 0; offset < GetSize(y); ++offset)
					if (!offsets[pos].count(offset))
						keep_b.append(b[branch * GetSize(y) + offset]);
			inputs.insert(keep_a.begin(), keep_a.end());
			inputs.insert(keep_b.begin(), keep_b.end());
			inputs.insert(select.begin(), select.end());
			if (cell->type == ID($mux))
				staging.addMux(NEW_ID, keep_a, keep_b, select, keep_y, cell->get_src_attribute());
			else
				staging.addPmux(NEW_ID, keep_a, keep_b, select, keep_y, cell->get_src_attribute());
		}
		pool<Cell *> candidates = encoding.cells;
		candidates.insert(replaced.begin(), replaced.end());
		candidates.insert(tree.producers.begin(), tree.producers.end());
		rewrite->removed = index.removable(candidates, replaced, outputs, inputs);
		bool removes_selection_logic = std::any_of(rewrite->removed.begin(), rewrite->removed.end(), [&](auto cell) {
			return !replaced.count(cell) || cell->type == ID($pmux);
		});
		if ((!shares_selection && !combines_selections && !removes_selection_logic) ||
				!std::all_of(replaced.begin(), replaced.end(), [&](auto cell) { return rewrite->removed.count(cell); }) || !rewrite->validate())
			return nullptr;
		return rewrite;
	}

	bool apply(std::unique_ptr<PmuxRewrite> rewrite)
	{
		if (!rewrite)
			return false;
		rewrite->commit();
		return true;
	}

	std::vector<Cell *> live_cells(const std::vector<IdString> &names)
	{
		std::vector<Cell *> result;
		for (auto name : names)
			if (auto cell = module->cell(name); cell && pmux_select_shape(cell) && index.editable(cell))
				result.push_back(cell);
		return result;
	}

	std::vector<Cell *> selected_choices()
	{
		auto cells = module->selected_cells();
		cells.erase(std::remove_if(cells.begin(), cells.end(), [&](auto cell) {
			return !pmux_select_shape(cell) || !index.editable(cell);
		}), cells.end());
		std::sort(cells.begin(), cells.end(), [](auto a, auto b) { return a->name < b->name; });
		return cells;
	}

	dict<SigSpec, std::vector<IdString>> encoded_groups()
	{
		dict<SigSpec, std::vector<IdString>> groups;
		for (auto cell : selected_choices()) {
			PmuxEncoding encoding(index);
			std::vector<int> rows;
			if (encoding.branch_table(index.port(cell, ID::S), rows))
				groups[pmux_control_key(encoding)].push_back(cell->name);
		}
		return groups;
	}

	bool rewrite_swap(const std::vector<Cell *> &cells, const PmuxEncoding &encoding, const std::vector<std::vector<int>> &tables)
	{
		PmuxSelectTree tree(index, encoding);
		std::vector<SwapColumn> columns;
		int rows = GetSize(tables.front());
		for (int i = 0; i < GetSize(cells); ++i) {
			auto a = index.port(cells[i], ID::A), b = index.port(cells[i], ID::B);
			int width = GetSize(a);
			if (GetSize(columns) + width > pmux_max_table_bits / rows)
				break;
			for (int offset = 0; offset < width; ++offset) {
				auto &column = columns.emplace_back(SwapColumn{i, offset, {}, {}});
				for (int row = 0; row < rows; ++row) {
					int branch = tables[i][row];
					SigBit bit = branch < 0 ? a[offset] : b[branch * width + offset];
					column.values.push_back(tree.fold(bit, row));
				}
			}
		}
		if (GetSize(columns) < 2)
			return false;
		for (int flip = 0; flip < GetSize(encoding.controls); ++flip)
			if (apply(swap_outputs(cells, encoding, tree, columns, flip)))
				return true;
		if (GetSize(encoding.controls) < 3)
			return false;
		SwapPartialCodes partial{encoding, {cells.begin(), cells.begin() + columns.back().cell + 1}, encoding.partial_codes(), std::nullopt};
		PmuxSelectTree raw_tree(index, encoding);
		for (auto &column : columns) {
			auto cell = cells[column.cell];
			const auto &a = cell->getPort(ID::A), &b = cell->getPort(ID::B);
			column.branch_values.push_back(raw_tree.literal(index.sigmap(a[column.offset])));
			for (int offset = column.offset; offset < GetSize(b); offset += GetSize(a))
				column.branch_values.push_back(raw_tree.literal(index.sigmap(b[offset])));
			for (int row = 0; row < rows; ++row)
				column.values[row] = column.branch_values[tables[column.cell][row] + 1];
		}
		for (int flip = 0; flip < GetSize(encoding.controls); ++flip)
			if (apply(swap_outputs(cells, encoding, raw_tree, columns, flip, &partial)))
				return true;
		return false;
	}

	template<typename Rewrite>
	bool rewrite_encoded_group(const std::vector<IdString> &names, Rewrite rewrite)
	{
		auto cells = live_cells(names);
		if (cells.empty())
			return false;
		std::vector<SigSpec> selects;
		for (auto cell : cells)
			selects.push_back(index.port(cell, ID::S));
		PmuxEncoding encoding(index);
		std::vector<std::vector<int>> tables;
		return encoding.branch_tables(selects, tables) && rewrite(cells, encoding, tables);
	}

	int share_exact_relations()
	{
		dict<std::pair<IdString, SigSpec>, std::vector<IdString>> exact;
		for (auto cell : selected_choices()) {
			SigSpec select = index.port(cell, ID::S);
			if (GetSize(select) <= 32)
				exact[{cell->type, select}].push_back(cell->name);
		}
		int changes = 0;
		for (const auto &[key, names] : exact) {
			auto matching = live_cells(names);
			auto control = index.sigmap(key.second);
			matching.erase(std::remove_if(matching.begin(), matching.end(), [&](auto cell) { return index.port(cell, ID::S) != control; }), matching.end());
			changes += apply(relations(matching));
		}
		return changes;
	}

	bool share_encoded_relations(std::vector<IdString> &names)
	{
		return rewrite_encoded_group(names, [&](const auto &cells, const auto &encoding, const auto &tables) {
			auto rewrite = relations(cells, &encoding, tables);
			if (!rewrite)
				return false;
			for (auto cell : rewrite->staging.cells())
				if (pmux_select_shape(cell))
					names.push_back(cell->name);
			return apply(std::move(rewrite));
		});
	}

	bool share_output_swaps(const std::vector<IdString> &names)
	{
		return rewrite_encoded_group(names, [&](const auto &cells, const auto &encoding, const auto &tables) {
			return rewrite_swap(cells, encoding, tables);
		});
	}

public:
	explicit RelationWorker(Module *module) : module(module), index(module) {}

	void run()
	{
		int before = module->cells_size();
		int changes = share_exact_relations();
		for (auto &[key, names] : encoded_groups()) {
			changes += share_encoded_relations(names);
			changes += share_output_swaps(names);
		}
		if (changes)
			log("  %s: shared selection output relations, RTLIL cell delta %+d.\n", log_id(module), module->cells_size() - before);
	}
};

struct OptPmuxRelPass : Pass {
	OptPmuxRelPass() : Pass("opt_pmux_rel", "share identical, complementary, and XOR-related selection outputs") {}

	void help() override
	{
		log("    opt_pmux_rel [selection]\n\n");
		log("Share selection outputs related by a fixed XOR or a swap under one control bit.\n");
		log("A swap can have one exceptional pair of encodings, corrected by local muxes.\n");
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

#include "passes/opt/pmux_rewrite.h"
#include "passes/opt/pmux_select_tree.h"

#include <numeric>
#include <ranges>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct Parity {
	std::vector<SigBit> terms;
	bool inverted = false, undef = false;

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
	if (a.undef || b.undef)
		return {{}, false, true};
	std::vector<SigBit> terms;
	std::set_symmetric_difference(a.terms.begin(), a.terms.end(), b.terms.begin(), b.terms.end(), std::back_inserter(terms));
	return {std::move(terms), a.inverted != b.inverted};
}

struct MuxArmTable {
	Cell *cell;
	SigSpec a, b, output, control;
	std::vector<int> rows;

	MuxArmTable(PmuxCoarseIndex &index, Cell *cell)
		: cell(cell), a(index.port(cell, ID::A)), b(index.port(cell, ID::B)), output(index.port(cell, ID::Y)),
		  control(index.port(cell, ID::S)), rows(arm_count())
	{
		std::iota(rows.begin(), rows.end(), 0);
	}

	int arm_count() const { return GetSize(control) + 1; }
	SigBit bit(int arm, int offset) const { return arm ? b[(arm - 1) * GetSize(output) + offset] : a[offset]; }

	template<typename Fn>
	auto map_rows(Fn fn) const
	{
		return std::views::iota(0, GetSize(rows)) | std::views::transform([this, fn](int row) { return fn(row, rows[row]); });
	}

	void emit_slice(Module &staging, const std::vector<int> &kept) const
	{
		if (kept.empty())
			return;
		SigSpec keep_a, keep_b, keep_y;
		for (int offset : kept) {
			keep_a.append(bit(0, offset));
			keep_y.append(output[offset]);
		}
		for (int arm = 1; arm < arm_count(); ++arm)
			for (int offset : kept)
				keep_b.append(bit(arm, offset));
		auto add = cell->type == ID($mux) ? &Module::addMux : &Module::addPmux;
		(staging.*add)(NEW_ID, keep_a, keep_b, control, keep_y, cell->get_src_attribute());
	}
};

template<typename Value>
struct ArmColumn {
	std::vector<Value> rows, arms;
	SigBit output;
	int selection;
};

struct Column : ArmColumn<Parity> {
	int term_count = 0, inversions = 0;
	const Column *reference = nullptr;
	Parity delta;
};

struct Selection {
	const MuxArmTable &table;
	std::vector<Column> columns;
	pool<Cell *> producers;
};

class RelationWorker
{
	Module *module;
	PmuxCoarseIndex index;

	dict<Cell *, std::pair<SigSpec, SigSpec>> operators;

	static std::optional<Parity> literal(SigBit bit)
	{
		if (bit.wire)
			return Parity{{bit}};
		if (bit == State::S0 || bit == State::S1)
			return Parity{{}, bit == State::S1};
		if (bit == State::Sx)
			return Parity{{}, false, true};
		return std::nullopt;
	}

	std::optional<Parity> arm_parity(SigBit bit, pool<Cell *> &region)
	{
		auto source = index.source(bit);
		if (!source || source->port != ID::Y || !source->cell->type.in(ID($xor), ID($xnor), ID($not)))
			return literal(bit);
		auto cell = source->cell;
		int width = GetSize(cell->getPort(ID::Y));
		if (width > 4096)
			return literal(bit);
		auto [entry, inserted] = operators.emplace(cell, std::pair<SigSpec, SigSpec>{});
		auto &[lhs, rhs] = entry->second;
		bool unary = cell->type == ID($not);
		if (inserted) {
			bool sign = pmux_is_signed_port(cell, ID::A) && (unary || pmux_is_signed_port(cell, ID::B));
			lhs = index.port(cell, ID::A);
			lhs.extend_u0(width, sign);
			if (!unary) {
				rhs = index.port(cell, ID::B);
				rhs.extend_u0(width, sign);
			}
		}
		auto a = literal(lhs[source->offset]);
		auto b = literal(unary ? SigBit(State::S0) : rhs[source->offset]);
		if (!a || !b || (!a->terms.empty() && a->terms == b->terms))
			return literal(bit);
		auto result = difference(*a, *b);
		if (!result.undef)
			result.inverted ^= cell->type != ID($xor);
		region.insert(cell);
		return result;
	}

	static bool preserves_inputs(const Parity &value, const Parity &base, const Parity &delta)
	{
		// 保留目标分支的数据依赖，避免为目标引入额外的未定义输入。
		auto includes = [&](const Parity &part) {
			return std::includes(value.terms.begin(), value.terms.end(), part.terms.begin(), part.terms.end());
		};
		return includes(base) && includes(delta);
	}

	static Parity condition(Parity value, PmuxPartialCode code, const dict<SigBit, int> &slots)
	{
		auto kept = std::remove_if(value.terms.begin(), value.terms.end(), [&](SigBit bit) {
			auto slot = slots.find(bit);
			if (slot == slots.end())
				return false;
			unsigned mask = 1u << slot->second;
			value.inverted ^= (code.one & mask) != 0;
			value.undef |= ((code.one | code.zero) & mask) == 0;
			return true;
		});
		value.terms.erase(kept, value.terms.end());
		return value;
	}

	struct PartialRows {
		const PmuxEncoding &encoding;
		std::vector<PmuxPartialCode> codes;
		std::vector<Cell *> cells;
		std::optional<std::vector<std::vector<PmuxBranchChoice>>> branches;

		explicit PartialRows(const PmuxEncoding &encoding) : encoding(encoding), codes(encoding.partial_codes()) {}

		const auto &choices()
		{
			log_assert(!cells.empty());
			if (!branches)
				branches = encoding.partial_branches(cells);
			return *branches;
		}
	};

	static bool partial_relation(const Column &base, const Column &other, const Parity &delta, PartialRows &partial)
	{
		const auto &slots = partial.encoding.slots();
		const auto &choices = partial.choices();
		unsigned full_mask = pmux_encoding_limit(GetSize(slots)) - 1;
		for (int row = 0; row < GetSize(partial.codes); ++row) {
			auto code = partial.codes[row];
			if ((code.one | code.zero) == full_mask)
				continue;
			const auto target = choices[other.selection][row];
			if (target.kind == BranchKind::Constant) {
				log_assert(target.val == State::Sx);
				continue;
			}
			bool target_dynamic = target.kind == BranchKind::Dynamic;
			Parity target_a = condition(other.arms[target_dynamic ? 0 : target.index], code, slots), target_b;
			if (target_dynamic)
				target_b = condition(other.arms[1], code, slots);
			// 单个 mux 的选择位未知时，任一分支未知都会使结果未知。
			if (target_a.undef || target_b.undef)
				continue;
			const auto source = choices[base.selection][row];
			if (source.kind == BranchKind::Constant) {
				log_assert(source.val == State::Sx);
				return false;
			}
			auto matches = [&](int branch) {
				Parity value = condition(base.arms[branch], code, slots);
				auto matches_target = [&](const Parity &expected) {
					return difference(value, expected) == delta && preserves_inputs(expected, value, delta);
				};
				return matches_target(target_a) || (target_dynamic && matches_target(target_b));
			};
			if (source.kind == BranchKind::Dynamic ? !(matches(0) && matches(1)) : !matches(source.index))
				return false;
		}
		return true;
	}

	std::vector<Selection> extract_columns(const std::vector<MuxArmTable> &tables, const dict<SigBit, int> &slots)
	{
		operators.clear();
		std::vector<Selection> selections;
		const unsigned mask = pmux_encoding_limit(GetSize(slots)) - 1;
		int inspected = 0;
		for (const auto &table : tables) {
			int arms = table.arm_count(), rows = GetSize(table.rows), width = GetSize(table.output);
			if (width > 4096)
				continue;
			inspected += std::max(rows, arms) * width;
			if (inspected > 65536)
				break;
			auto &selection = selections.emplace_back(Selection{table, {}, {}});
			for (int offset = 0; offset < width; ++offset) {
				auto &column = selection.columns.emplace_back();
				column.output = table.output[offset];
				column.selection = GetSize(selections) - 1;
				for (int arm = 0; arm < arms; ++arm) {
					auto value = arm_parity(table.bit(arm, offset), selection.producers);
					if (!value)
						break;
					column.arms.push_back(std::move(*value));
				}
				if (GetSize(column.arms) != arms)
					continue;
				for (auto value : table.map_rows([&](int row, int arm) {
						 return condition(column.arms[arm], {mask ^ unsigned(row), unsigned(row)}, slots);
					 })) {
					column.term_count += GetSize(value.terms);
					column.inversions += value.inverted;
					column.rows.push_back(std::move(value));
				}
			}
		}
		return selections;
	}

	std::vector<const Column *> solve_relations(std::vector<Selection> &selections, const PmuxEncoding *encoding)
	{
		std::vector<Column *> columns;
		for (auto &selection : selections)
			for (auto &column : selection.columns)
				if (!column.rows.empty())
					columns.push_back(&column);
		std::stable_sort(columns.begin(), columns.end(), [](const Column *a, const Column *b) {
			return std::tie(a->term_count, a->inversions) < std::tie(b->term_count, b->inversions);
		});
		dict<std::vector<Parity>, std::vector<std::pair<const Column *, const Parity *>>> groups;
		std::vector<const Column *> matches;
		std::optional<PartialRows> partial;
		auto partial_match = [&](const Column &base, const Column &target, const Parity &delta) {
			if (!partial) {
				partial.emplace(*encoding);
				for (const auto &selection : selections)
					partial->cells.push_back(selection.table.cell);
			}
			return partial_relation(base, target, delta, *partial);
		};
		for (auto column : columns) {
			auto first = std::find_if(column->rows.begin(), column->rows.end(), [](const Parity &row) { return !row.undef; });
			if (first == column->rows.end())
				continue;
			std::vector<Parity> signature;
			for (const auto &row : column->rows)
				signature.push_back(difference(row, *first));
			auto &bases = groups[signature];
			for (auto [base, value] : bases) {
				auto delta = difference(*value, *first);
				bool usable = std::equal(column->rows.begin(), column->rows.end(), base->rows.begin(), [&](const Parity &row, const Parity &basis) {
					return row.undef || preserves_inputs(row, basis, delta);
				});
				if (!usable || (encoding && !partial_match(*base, *column, delta)))
					continue;
				column->reference = base;
				column->delta = std::move(delta);
				matches.push_back(column);
				break;
			}
			if (!column->reference && GetSize(bases) < 32)
				bases.emplace_back(column, &*first);
		}
		return matches;
	}

	std::unique_ptr<PmuxRewrite> relations(const std::vector<Selection> &selections, const std::vector<const Column *> &columns,
			const pool<Cell *> &producers, const char *rule)
	{
		if (columns.empty())
			return nullptr;
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, rule);
		auto &staging = rewrite->staging;
		pool<Cell *> candidates, replaced;
		for (const auto &selection : selections) {
			std::vector<int> kept;
			for (int offset = 0; offset < GetSize(selection.columns); ++offset)
				if (!selection.columns[offset].reference)
					kept.push_back(offset);
			if (kept.size() == selection.columns.size())
				continue;
			replaced.insert(selection.table.cell);
			candidates.insert(selection.producers.begin(), selection.producers.end());
			selection.table.emit_slice(staging, kept);
		}
		candidates.insert(replaced.begin(), replaced.end());
		candidates.insert(producers.begin(), producers.end());
		struct ParityPlan {
			std::vector<SigSpec> operands;
			SigSpec y;
		};
		idict<std::pair<int, bool>> forms;
		std::vector<ParityPlan> relations;
		for (auto column : columns) {
			const auto &delta = column->delta;
			int terms = GetSize(delta.terms);
			int form = forms({terms, delta.inverted});
			if (form == GetSize(relations))
				relations.emplace_back(ParityPlan{std::vector<SigSpec>(terms + 1), {}});
			auto &relation = relations[form];
			relation.operands[0].append(column->reference->output);
			for (int term = 0; term < terms; ++term)
				relation.operands[term + 1].append(delta.terms[term]);
			relation.y.append(column->output);
		}
		for (int form = GetSize(forms); form-- > 0;) {
			const auto &[terms, inverted] = forms[form];
			const auto &relation = relations[form];
			SigSpec left = relation.operands.front();
			if (!terms) {
				if (inverted)
					staging.addNot(NEW_ID, left, relation.y);
				else
					rewrite->connect(relation.y, left);
				continue;
			}
			for (int term = 1; term <= terms; ++term) {
				bool final = term == terms;
				SigSpec output = final ? relation.y : SigSpec(staging.addWire(NEW_ID, GetSize(relation.y)));
				auto add = final && inverted ? &Module::addXnor : &Module::addXor;
				(staging.*add)(NEW_ID, left, relation.operands[term], output, false, "");
				left = std::move(output);
			}
		}
		rewrite->find_removable(candidates, replaced);
		for (auto cell : replaced)
			if (!rewrite->removed.count(cell))
				return nullptr;
		return rewrite->validate() ? std::move(rewrite) : nullptr;
	}

	using SwapColumn = ArmColumn<int>;

	struct SwapPair {
		int first, second;
		std::optional<int> exception;
	};

	static bool preserves_partial_swap(const SwapColumn &column, const SwapColumn &other,
			const std::vector<PmuxBranchChoice> &choices, const std::vector<int> &affected, int low, int high)
	{
		for (int row : affected) {
			const auto choice = choices[row];
			if (choice.kind == BranchKind::Constant) {
				log_assert(choice.val == State::Sx);
				continue;
			}
			// 交换位未知时，局部修正和外层交换可能选中对方在例外编码的数据。
			auto preserves = [&](int value) {
				if (choice.kind == BranchKind::Dynamic)
					return value == column.arms[0] || value == column.arms[1];
				return value == column.arms[choice.index];
			};
			if (!preserves(other.rows[low]) || !preserves(other.rows[high]))
				return false;
		}
		return true;
	}

	static std::vector<SwapPair> swap_pairs(const std::vector<SwapColumn> &columns, int mask, PartialRows *partial)
	{
		std::vector<SwapPair> pairs;
		std::vector<bool> used(columns.size());
		int budget = pmux_max_pair_checks;
		int rows = GetSize(columns.front().rows);
		for (int candidate = 0; candidate < (partial ? rows : 1); ++candidate) {
			std::optional<std::pair<int, int>> except;
			std::vector<int> affected;
			if (partial) {
				if (candidate & mask)
					continue;
				except.emplace(candidate, candidate | mask);
				for (int row = 0; row < GetSize(partial->codes); ++row) {
					const auto &code = partial->codes[row];
					unsigned fixed = code.zero | code.one;
					if (!(fixed & mask) && (unsigned(candidate) & fixed) == code.one)
						affected.push_back(row);
				}
			}
			dict<SwapSignature, std::vector<int>> groups;
			for (int col = 0; col < GetSize(columns); ++col)
				if (!used[col])
					groups[SwapSignature(columns[col].rows, except, 0)].push_back(col);

			for (int col = 0; col < GetSize(columns); ++col) {
				if (used[col])
					continue;
				const auto &a = columns[col];
				auto partners = groups.find(SwapSignature(a.rows, except, mask));
				if (partners == groups.end() || (!partial && std::binary_search(partners->second.begin(), partners->second.end(), col)))
					continue;
				for (int partner : partners->second) {
					if (partner == col || used[partner])
					continue;
					const auto &b = columns[partner];
					if (except) {
						if ((budget -= 1 + GetSize(affected)) < 0)
							return pairs;
						const auto [low_row, high_row] = *except;
						if (a.rows[low_row] == b.rows[high_row] && a.rows[high_row] == b.rows[low_row])
							continue;
						const auto &branches = partial->choices();
						if (!preserves_partial_swap(a, b, branches[a.selection], affected, low_row, high_row) ||
								!preserves_partial_swap(b, a, branches[b.selection], affected, low_row, high_row))
							continue;
					}
					used[col] = used[partner] = true;
					pairs.push_back({col, partner, partial ? std::optional(candidate) : std::nullopt});
					break;
				}
			}
		}
		return pairs;
	}

	std::unique_ptr<PmuxRewrite> swap_outputs(const std::vector<MuxArmTable> &tables, const PmuxEncoding &encoding,
			PmuxSelectTree &tree, const std::vector<SwapColumn> &columns, const std::vector<int> &starts, int flip, PartialRows *partial)
	{
		pool<Cell *> replaced;
		std::vector<int> controls, natural_order, roots, reference;
		std::vector<std::vector<int>> offsets(tables.size());
		SigSpec swap_y;
		bool shares_selection = false;
		if (partial)
			controls.push_back(flip);
		for (int control = 0; control < GetSize(encoding.controls()); ++control) {
			natural_order.push_back(control);
			if (control != flip)
				controls.push_back(control);
		}
		int mask = 1 << flip;
		for (const auto &pair : swap_pairs(columns, mask, partial)) {
			const auto &a = columns[pair.first];
			const auto &b = columns[pair.second];
			auto shared_column = [&](const SwapColumn &first, const SwapColumn &second) {
				std::vector<int> values;
				for (int row = 0; row < GetSize(first.rows); ++row) {
					if (row & mask)
						continue;
					values.push_back(first.rows[row]);
					if (pair.exception)
						values.push_back(row == *pair.exception ? second.rows[row | mask] : first.rows[row]);
				}
				shares_selection |= std::adjacent_find(values.begin(), values.end(), std::not_equal_to<int>{}) != values.end();
				return tree.column(std::move(values), controls);
			};
			int left = shared_column(a, b);
			int right = shared_column(b, a);
			int level = GetSize(controls);
			roots.push_back(tree.select(flip, level, left, right));
			roots.push_back(tree.select(flip, level, right, left));
			for (int column : {pair.first, pair.second}) {
				const auto &entry = columns[column];
				if (partial)
					reference.push_back(tree.column(entry.rows, natural_order));
				swap_y.append(entry.output);
				replaced.insert(tables[entry.selection].cell);
				offsets[entry.selection].push_back(column - starts[entry.selection]);
			}
		}
		if (roots.empty())
			return nullptr;
		auto live = tree.analyze(roots);
		if (partial && live.mux_bits >= tree.analyze(reference).mux_bits)
			return nullptr;
		auto rewrite = std::make_unique<PmuxRewrite>(module, index, "encoded_output_swap");
		auto &staging = rewrite->staging;
		rewrite->connect(swap_y, tree.emit(&staging, roots, tables.front().cell->get_src_attribute(), live));
		bool combines_selections = GetSize(replaced) > 1;
		for (int pos = 0; pos < GetSize(tables); ++pos) {
			if (offsets[pos].empty())
				continue;
			auto &skip = offsets[pos];
			std::sort(skip.begin(), skip.end());
			std::vector<int> kept;
			for (int offset = 0; offset < GetSize(tables[pos].output); ++offset)
				if (!std::binary_search(skip.begin(), skip.end(), offset))
					kept.push_back(offset);
			combines_selections &= kept.empty();
			tables[pos].emit_slice(staging, kept);
		}
		pool<Cell *> candidates = encoding.cells();
		candidates.insert(replaced.begin(), replaced.end());
		candidates.insert(tree.producers.begin(), tree.producers.end());
		rewrite->find_removable(candidates, replaced);
		bool removes_selection_logic = std::any_of(rewrite->removed.begin(), rewrite->removed.end(), [&](auto cell) {
			return !replaced.count(cell) || cell->type == ID($pmux);
		});
		if ((!shares_selection && !combines_selections && !removes_selection_logic) ||
				!std::all_of(replaced.begin(), replaced.end(), [&](auto cell) { return rewrite->removed.count(cell); }) || !rewrite->validate())
			return nullptr;
		return rewrite;
	}

	struct SwapSignature {
		const std::vector<int> *values;
		std::optional<std::pair<int, int>> exception;
		int flip;
		Hasher::hash_t fingerprint;

		SwapSignature(const std::vector<int> &values, std::optional<std::pair<int, int>> exception, int flip)
			: values(&values), exception(exception), flip(flip)
		{
			Hasher hash;
			for (int row = 0; row < GetSize(values); ++row)
				if (!ignored(row))
					hash.eat(values[row ^ flip]);
			fingerprint = hash.yield();
		}

		bool ignored(int row) const { return exception && (row == exception->first || row == exception->second); }

		bool operator==(const SwapSignature &other) const
		{
			if (fingerprint != other.fingerprint || exception != other.exception || values->size() != other.values->size())
				return false;
			for (int row = 0; row < GetSize(*values); ++row)
				if (!ignored(row) && (*values)[row ^ flip] != (*other.values)[row ^ other.flip])
					return false;
			return true;
		}

		Hasher hash_into(Hasher hash) const
		{
			hash.eat(fingerprint);
			return hash;
		}
	};

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

	bool rewrite_swap(const PmuxEncoding &encoding, const std::vector<MuxArmTable> &tables)
	{
		int rows = GetSize(tables.front().rows);
		int controls = GetSize(encoding.controls());
		for (bool allow_exception : {false, true}) {
			if (allow_exception && controls < 3)
				break;
			PmuxSelectTree tree(index, encoding);
			std::vector<SwapColumn> columns;
			std::vector<int> starts;
			std::optional<PartialRows> partial;
			if (allow_exception)
				partial.emplace(encoding);
			for (const auto &table : tables) {
				int width = GetSize(table.output);
				if (GetSize(columns) + width > pmux_max_table_bits / rows)
					break;
				int selection = GetSize(starts);
				starts.push_back(GetSize(columns));
				if (partial)
					partial->cells.push_back(table.cell);
				for (int offset = 0; offset < width; ++offset) {
					auto &column = columns.emplace_back(SwapColumn{{}, {}, table.output[offset], selection});
					if (partial)
						for (int arm = 0; arm < table.arm_count(); ++arm)
							column.arms.push_back(tree.literal(table.bit(arm, offset)));
					auto values = table.map_rows([&](int row, int arm) {
						return partial ? column.arms[arm] : tree.fold(table.bit(arm, offset), row);
					});
					for (int value : values)
						column.rows.push_back(value);
				}
			}
			if (GetSize(columns) < 2)
				return false;
			for (int flip = 0; flip < controls; ++flip)
				if (apply(swap_outputs(tables, encoding, tree, columns, starts, flip, partial ? &*partial : nullptr)))
					return true;
		}
		return false;
	}

	std::vector<MuxArmTable> encoded_tables(const std::vector<IdString> &names, PmuxEncoding &encoding)
	{
		std::vector<MuxArmTable> tables;
		std::vector<SigSpec> selects;
		for (auto cell : live_cells(names))
			selects.push_back(tables.emplace_back(index, cell).control);
		std::vector<std::vector<int>> rows;
		if (!encoding.branch_tables(selects, rows))
			return {};
		for (int i = 0; i < GetSize(rows); ++i)
			tables[i].rows = std::move(rows[i]);
		return tables;
	}

	int share_exact_relations()
	{
		idict<std::pair<IdString, SigSpec>> keys;
		std::vector<std::vector<IdString>> exact;
		for (auto cell : selected_choices()) {
			SigSpec select = index.port(cell, ID::S);
			if (GetSize(select) > 32)
				continue;
			int group = keys({cell->type, select});
			if (group == GetSize(exact))
				exact.emplace_back();
			exact[group].push_back(cell->name);
		}
		int changes = 0;
		for (int group = GetSize(exact); group-- > 0;) {
			auto control = index.sigmap(keys[group].second);
			std::vector<MuxArmTable> tables;
			for (auto cell : live_cells(exact[group]))
				if (index.port(cell, ID::S) == control)
					tables.emplace_back(index, cell);
			auto selections = extract_columns(tables, {});
			changes += apply(relations(selections, solve_relations(selections, nullptr), {}, "output_relation"));
		}
		return changes;
	}

	int rewrite_encoded_group(std::vector<IdString> &names)
	{
		PmuxEncoding encoding(index);
		auto tables = encoded_tables(names, encoding);
		if (tables.empty())
			return 0;
		auto selections = extract_columns(tables, encoding.slots());
		auto rewrite = relations(selections, solve_relations(selections, &encoding), encoding.cells(), "encoded_output_relation");
		if (!rewrite)
			return rewrite_swap(encoding, tables);
		for (auto cell : rewrite->staging.cells())
			if (pmux_select_shape(cell))
				names.push_back(cell->name);
		rewrite->commit();
		PmuxEncoding updated(index);
		auto updated_tables = encoded_tables(names, updated);
		return 1 + (!updated_tables.empty() && rewrite_swap(updated, updated_tables));
	}

public:
	explicit RelationWorker(Module *module) : module(module), index(module) {}

	int run()
	{
		int before = module->cells_size();
		int changes = share_exact_relations();
		idict<SigSpec> keys;
		std::vector<std::vector<IdString>> encoded;
		for (auto cell : selected_choices()) {
			PmuxEncoding encoding(index);
			std::vector<int> rows;
			if (!encoding.branch_table(index.port(cell, ID::S), rows))
				continue;
			int group = keys(encoding.control_key());
			if (group == GetSize(encoded))
				encoded.emplace_back();
			encoded[group].push_back(cell->name);
		}
		for (int group = GetSize(encoded); group-- > 0;)
			changes += rewrite_encoded_group(encoded[group]);
		if (changes)
			log("  %s: shared selection output relations, RTLIL cell delta %+d.\n", log_id(module), module->cells_size() - before);
		return changes;
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
		pmux_run_pass(design, "opt_pmux_rel", "Executing OPT_PMUX_REL pass.\n", [&](Module *module) {
			return RelationWorker(module).run();
		});
	}
} OptPmuxRelPass;

PRIVATE_NAMESPACE_END

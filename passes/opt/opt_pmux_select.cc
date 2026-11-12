#include "kernel/yosys.h"
#include "passes/opt/pmux_coarse.h"

#include <array>
#include <cstdint>
#include <optional>
#include <tuple>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

constexpr int max_controls = 6;
constexpr int max_rows = 1 << max_controls;
constexpr int max_table_bits = 32768;

// 每一位对应一种控制编码，按控制输入的索引从低位开始排列。
constexpr std::array<uint64_t, max_controls> control_patterns = {
	0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
	0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000,
};

struct SelectDecoder
{
	PmuxCoarseIndex &index;
	std::vector<SigBit> controls;
	dict<SigBit, int> slots;
	dict<SigBit, uint64_t> decoded;
	pool<SigBit> active;
	pool<Cell *> cells;

	explicit SelectDecoder(PmuxCoarseIndex &index) : index(index) {}

	std::optional<uint64_t> literal(SigBit bit)
	{
		if (!bit.wire) {
			if (bit == State::S0)
				return 0;
			if (bit == State::S1)
				return ~uint64_t(0);
			return std::nullopt;
		}
		auto slot = slots.find(bit);
		if (slot != slots.end())
			return control_patterns[slot->second];
		if (GetSize(controls) == max_controls)
			return std::nullopt;
		int position = GetSize(controls);
		controls.push_back(bit);
		slots[bit] = position;
		return control_patterns[position];
	}

	std::optional<uint64_t> comparison(Cell *cell)
	{
		auto operands = index.comparison_operands(cell, max_rows);
		if (!operands)
			return std::nullopt;
		const auto &[a, b] = *operands;

		uint64_t equal = ~uint64_t(0);
		for (int i = 0; i < GetSize(a); i++) {
			auto lhs = literal(a[i]), rhs = literal(b[i]);
			if (!lhs || !rhs)
				return std::nullopt;
			equal &= ~(*lhs ^ *rhs);
		}
		return cell->type == ID($ne) ? ~equal : equal;
	}

	std::optional<uint64_t> gate(Cell *cell, int depth)
	{
		if (cell->type.in(ID($eq), ID($ne), ID($logic_not)))
			return comparison(cell);
		auto a = index.port(cell, ID::A);
		if (GetSize(a) > max_rows)
			return std::nullopt;
		if (cell->type.in(ID($reduce_or), ID($reduce_bool), ID($reduce_and))) {
			bool is_and = cell->type == ID($reduce_and);
			uint64_t result = is_and ? ~uint64_t(0) : 0;
			for (auto bit : a) {
				auto input = decode(bit, depth - 1);
				if (!input)
					return std::nullopt;
				result = is_and ? result & *input : result | *input;
			}
			return result;
		}
		if (GetSize(a) != 1)
			return std::nullopt;
		auto lhs = decode(a[0], depth - 1);
		if (!lhs)
			return std::nullopt;
		if (cell->type == ID($not))
			return ~*lhs;
		auto b = index.port(cell, ID::B);
		if (GetSize(b) != 1)
			return std::nullopt;
		auto rhs = decode(b[0], depth - 1);
		if (!rhs)
			return std::nullopt;
		if (cell->type == ID($and))
			return *lhs & *rhs;
		if (cell->type == ID($or))
			return *lhs | *rhs;
		return *lhs ^ *rhs;
	}

	std::optional<uint64_t> decode(SigBit bit, int depth = 12)
	{
		auto found = decoded.find(bit);
		if (found != decoded.end())
			return found->second;
		auto source = index.source(bit);
		if (!source || source->port != ID::Y || GetSize(source->cell->getPort(ID::Y)) != 1)
			return literal(bit);
		auto cell = source->cell;
		if (!cell->type.in(ID($eq), ID($ne), ID($logic_not), ID($reduce_or), ID($reduce_bool),
				ID($reduce_and), ID($not), ID($and), ID($or), ID($xor)))
			return literal(bit);
		if (depth == 0 || GetSize(cells) >= 128 || !active.insert(bit).second)
			return std::nullopt;
		auto result = gate(cell, depth);
		active.erase(bit);
		if (result) {
			cells.insert(cell);
			decoded[bit] = *result;
		}
		return result;
	}

	bool branch_table(const SigSpec &select, std::vector<int> &branches)
	{
		std::vector<uint64_t> truth;
		for (auto bit : select) {
			auto value = decode(bit);
			if (!value)
				return false;
			truth.push_back(*value);
		}
		int rows = 1 << GetSize(controls);
		uint64_t valid_rows = rows == max_rows ? ~uint64_t(0) : (uint64_t(1) << rows) - 1;
		uint64_t seen = 0;
		branches.assign(rows, -1);
		for (int i = 0; i < GetSize(truth); i++) {
			uint64_t active_rows = truth[i] & valid_rows;
			if (seen & active_rows)
				return false;
			seen |= active_rows;
			for (int code = 0; code < rows; code++)
				if (active_rows & (uint64_t(1) << code))
					branches[code] = i;
		}
		return true;
	}
};

struct SelectTree
{
	struct Node {
		SigBit leaf;
		int control;
		int low;
		int high;
	};

	const SelectDecoder &decoder;
	std::vector<Node> nodes;
	dict<SigBit, int> leaves;
	dict<std::tuple<int, int, int>, int> muxes;
	std::array<std::vector<int>, max_controls> levels;
	std::vector<int> roots;
	pool<SigBit> inputs;

	explicit SelectTree(const SelectDecoder &decoder) : decoder(decoder) {}

	int leaf(SigBit bit)
	{
		auto found = leaves.find(bit);
		if (found != leaves.end())
			return found->second;
		int node = GetSize(nodes);
		nodes.push_back({bit, -1, -1, -1});
		leaves[bit] = node;
		return node;
	}

	int mux(int control, int low, int high)
	{
		if (low == high)
			return low;
		if (nodes[low].control < 0 && nodes[low].leaf == State::S0 &&
				nodes[high].control < 0 && nodes[high].leaf == State::S1)
			return leaf(decoder.controls[control]);
		auto key = std::make_tuple(control, low, high);
		auto found = muxes.find(key);
		if (found != muxes.end())
			return found->second;
		int node = GetSize(nodes);
		nodes.push_back({SigBit(), control, low, high});
		muxes[key] = node;
		return node;
	}

	void append(const std::vector<SigSpec> &rows)
	{
		std::array<int, max_rows> column;
		for (int offset = 0; offset < GetSize(rows.front()); offset++) {
			for (int code = 0; code < GetSize(rows); code++) {
				auto bit = rows[code][offset];
				auto control = decoder.slots.find(bit);
				if (control != decoder.slots.end())
					bit = (code & (1 << control->second)) ? State::S1 : State::S0;
				column[code] = leaf(bit);
			}
			for (int level = 0, size = GetSize(rows) / 2; size != 0; level++, size /= 2)
				for (int i = 0; i < size; i++)
					column[i] = mux(level, column[2 * i], column[2 * i + 1]);
			roots.push_back(column[0]);
		}
	}

	std::pair<int, int> count_muxes()
	{
		int mux_bits = 0;
		pool<int> seen;
		std::vector<int> remaining = roots;
		while (!remaining.empty()) {
			int id = remaining.back();
			remaining.pop_back();
			if (!seen.insert(id).second)
				continue;
			const auto &node = nodes[id];
			if (node.control < 0) {
				if (node.leaf.wire)
					inputs.insert(node.leaf);
				continue;
			}
			levels[node.control].push_back(id);
			mux_bits++;
			inputs.insert(decoder.controls[node.control]);
			remaining.push_back(node.low);
			remaining.push_back(node.high);
		}
		int mux_cells = std::count_if(levels.begin(), levels.end(), [](const auto &level) { return !level.empty(); });
		return {mux_cells, mux_bits};
	}

	SigSpec emit(Module *module, const std::string &src) const
	{
		std::vector<SigBit> signals(GetSize(nodes));
		for (const auto &entry : leaves)
			signals[entry.second] = entry.first;
		for (int control = 0; control < GetSize(decoder.controls); control++) {
			const auto &level = levels[control];
			if (level.empty())
				continue;
			SigSpec a, b;
			Wire *wire = module->addWire(NEW_ID, GetSize(level));
			for (int i = 0; i < GetSize(level); i++) {
				int id = level[i];
				a.append(signals[nodes[id].low]);
				b.append(signals[nodes[id].high]);
				signals[id] = SigBit(wire, i);
			}
			module->addMux(NEW_ID, a, b, decoder.controls[control], wire, src);
		}
		SigSpec result;
		for (int id : roots)
			result.append(signals[id]);
		return result;
	}
};

bool select_shape(Cell *cell)
{
	if (!cell->type.in(ID($mux), ID($pmux)))
		return false;
	int width = GetSize(cell->getPort(ID::Y));
	int branches = GetSize(cell->getPort(ID::S));
	return width > 0 && width <= max_table_bits && branches > 0 && branches <= max_rows &&
		GetSize(cell->getPort(ID::A)) == width && GetSize(cell->getPort(ID::B)) == width * branches &&
		(cell->type == ID($pmux) || branches == 1);
}

int rebuild_selection(PmuxCoarseIndex &index, const std::vector<Cell *> &cells)
{
	SelectDecoder decoder(index);
	auto select = index.port(cells.front(), ID::S);
	std::vector<int> branches;
	if (!decoder.branch_table(select, branches))
		return 0;
	int total_width = 0;
	for (auto cell : cells) {
		if (!index.editable(cell) || index.port(cell, ID::S) != select)
			return 0;
		int width = GetSize(cell->getPort(ID::Y));
		if (width > max_table_bits / GetSize(branches) - total_width)
			return 0;
		total_width += width;
	}

	SelectTree tree(decoder);
	SigSpec output;
	std::string src;
	pool<Cell *> replaced;
	for (auto cell : cells) {
		int width = GetSize(cell->getPort(ID::Y));
		auto a = index.port(cell, ID::A);
		auto b = index.port(cell, ID::B);
		std::vector<SigSpec> rows;
		for (int branch : branches)
			rows.push_back(branch == -1 ? a : b.extract(branch * width, width));
		tree.append(rows);
		output.append(cell->getPort(ID::Y));
		if (src.empty())
			src = cell->get_src_attribute();
		replaced.insert(cell);
	}
	auto [added, mux_bits] = tree.count_muxes();
	// 单路条件本身已经共享，仅在减少数据选择节点时展开它。
	if (GetSize(select) == 1 && mux_bits >= total_width)
		return 0;
	pool<SigBit> outputs;
	for (auto bit : index.sigmap(output))
		outputs.insert(bit);
	if (!index.independent(tree.inputs, outputs))
		return 0;

	pool<Cell *> candidates = decoder.cells;
	candidates.insert(replaced.begin(), replaced.end());
	auto removed = index.removable(candidates, replaced, outputs, tree.inputs);
	if (GetSize(removed) <= added)
		return 0;
	for (auto cell : cells)
		if (!removed.count(cell))
			return 0;

	for (auto cell : removed)
		index.module->remove(cell);
	index.module->connect(output, tree.emit(index.module, src));
	return GetSize(removed) - added;
}

struct OptPmuxSelectPass : Pass
{
	OptPmuxSelectPass() : Pass("opt_pmux_select", "rebuild selection networks from decoded control signals") {}

	void help() override
	{
		log("\n");
		log("    opt_pmux_select [selection]\n");
		log("\n");
		log("Recover binary control signals from mutually exclusive select conditions.\n");
		log("Share mux stages across output fields and remove redundant decode logic\n");
		log("when the replacement reduces the number of RTLIL cells.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing OPT_PMUX_SELECT pass (rebuild selection networks).\n");
		extra_args(args, 1, design);
		if (pmux_coarse_observes_undef(design))
			return;
		int rewrites = 0, savings = 0;
		for (auto module : design->selected_modules()) {
			if (module->has_processes())
				continue;
			std::vector<Cell *> candidates;
			for (auto cell : module->selected_cells())
				if (select_shape(cell))
					candidates.push_back(cell);
			if (candidates.empty())
				continue;
			PmuxCoarseIndex index(module);
			dict<SigSpec, std::vector<Cell *>> groups;
			for (auto cell : candidates)
				if (index.editable(cell))
					groups[index.port(cell, ID::S)].push_back(cell);
			for (const auto &group : groups) {
				int saved = group.second.size() > 1 ? rebuild_selection(index, group.second) : 0;
				if (saved) {
					rewrites++;
					savings += saved;
					continue;
				}
				for (auto cell : group.second) {
					saved = rebuild_selection(index, {cell});
					rewrites += saved != 0;
					savings += saved;
				}
			}
		}
		log("Rebuilt %d selection networks and removed %d net RTLIL cells.\n", rewrites, savings);
	}
} OptPmuxSelectPass;

PRIVATE_NAMESPACE_END

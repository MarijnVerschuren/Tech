from operator import itemgetter
from typing import *
import pandas as pd
import json
import sys



class InputError(Exception):
	"""problems with the command line input"""


class Node:
	def __init__(self, num: int, critical=False):
		self.num = num
		self.critical = critical
		self.occupied = False
		self.neighbors: List[Tuple["Node", int]] = []

	def get_travel_cost(self, to: "Node") -> int:
		if to_node := [n[1] for n in self.neighbors if n[0] == to]:
			return to_node[0]
		return 0

	def __str__(self) -> str:	return f"{'*' if self.critical else ''}({self.num})"
	def __repr__(self) -> str:	return str(self)

	def __eq__(self, other: int or "Node") -> bool:
		if type(other) == Node:
			return self.num == other.num
		return self.num == other


class Player:
	def __init__(self, start: Node, end: Node, lookup_fn: callable, budget: int, playable: bool = False):
		self.start = start
		self.end = end
		self.node = start
		self.lookup = lookup_fn
		self.budget_left = budget
		self.move_queue = None
		if not playable: return
		self.move_queue = self.lookup(self.start, self.end)[2][1:]

	def is_move_illegal(self, to_node: Node) -> str:
		if to_node.occupied and to_node.critical:
			return "node is critical and occupied"
		if to_node not in [n[0] for n in self.node.neighbors] + [self.node]:
			return "node is unconnected to current"
		if self.budget_left - self.node.get_travel_cost(to_node) < 0:
			return "too expensive"
		return ""


	def move(self, to: Node = None) -> bool:
		if to:
			print(id(to))
			if reason := self.is_move_illegal(to):
				print(f"Invalid move: {self.node.num} -> {to.num}: {reason}.")
				return False
			self.budget_left -= self.node.get_travel_cost(to)
			self.node = to
			return True

		if not self.move_queue: return False
		next_node = self.move_queue.pop(0)

		print(id(next_node))
		if next_node == self.node:
			return True

		if self.is_move_illegal(next_node):
			alts = [self.lookup(n, self.end) for n in self.node.neighbors]
			alt = None
			for a in alts:
				if len(a) > len(self.move_queue): continue
				if not alt or len(a) < len(alt):
					alt = a
			if alt:
				self.move_queue = alt
				next_node = self.move_queue.pop(0)
			else: next_node = self.node


		self.node.occupied = False
		self.budget_left -= self.node.get_travel_cost(next_node)
		self.node = next_node
		self.node.occupied = True

		return True


	def __str__(self) -> str:	return f"at {self.node} on path: {self.move_queue}"
	def __repr__(self) -> str:	return str(self)


def get_path(from_node: int, shortest_paths: Dict[int, Tuple[Node, int]]) -> List[Node]:
	if from_node not in shortest_paths:
		return []

	if shortest_paths[from_node][0] == from_node:  # At start node
		return [get_node(nodes, from_node)]

	if not shortest_paths[from_node][0]:
		return []

	if path := get_path(shortest_paths[from_node][0].num, shortest_paths):
		return path + [get_node(nodes, from_node)]

	return []


def get_node(nodes: List[Node], num: int) -> Node: return nodes[nodes.index(num)]


def get_shortest_paths(nodes: List[Node], start: Node, budget: int) -> Dict[int, Tuple[Node, int]]:  # Result: O((M+1)N)
	shortest_paths = {node.num: (None, float('inf'), float('inf')) for node in nodes}  # Node: (from, cost). O(N)
	shortest_paths[start.num] = (start.num, 0, 0)

	queue = [start]

	while queue:  # Result: O(MN)
		current_node = queue.pop(0)  # O(N), since all elements have to be shifted.

		for neighbor, cost in current_node.neighbors:  # O(M)
			new_dist = shortest_paths[current_node.num][1] + 1
			new_cost = shortest_paths[current_node.num][2] + cost

			if new_dist < shortest_paths[neighbor.num][1] and new_cost <= budget:
				shortest_paths[neighbor.num] = (current_node, new_dist, new_cost)
				queue.append(neighbor)

	return shortest_paths


def dijkstra(nodes: List[Node], budget: int) -> pd.DataFrame:  # Result: O((M+2)N)
	results = pd.DataFrame(columns=['from', 'to', 'path', 'distance', 'cost'])

	for start in nodes:
		shortest_paths = get_shortest_paths(nodes, start, budget)  # O((M+1)N)

		for node, (from_node, dist, cost) in shortest_paths.items():  # O(N)
			results.loc[len(results.index)] = [start.num, node, get_path(node, shortest_paths), dist, cost]

	return results


if __name__ == '__main__':
	if "-file" not in sys.argv:
		raise InputError("input file not provided")
	if not ("-white" or "-black" in sys.argv):
		raise InputError("player not provided")
	file = sys.argv[sys.argv.index("-file") + 1]
	is_white = "-white" in sys.argv

	try:
		with open(file, "r") as file:
			data = json.load(file)

		locations, roads, start_node, budget = itemgetter("Locations", "Roads", "StartLocation", "Budget")(data)
		nodes = [Node(n, n in locations["critical"]) for n in list(set(roads["a"] + roads["b"]))]
		start_node = nodes[nodes.index(start_node)]; end = None
		for start, end, price in zip(roads["a"], roads["b"], roads["price"]):
			start = nodes[nodes.index(start)]
			end = nodes[nodes.index(end)]
			start.neighbors.append((end, price))
			end.neighbors.append((start, price))
	except:
		raise InputError("input file has the wrong format")

	table = dijkstra(nodes, budget)
	t_lookup = lambda x, y: table.loc[(table["from"] == x) & (table["to"] == y)].values[0]
	n_lookup = lambda x: nodes[nodes.index(x)]

	white = Player(start_node, end, t_lookup, budget, is_white)
	black = Player(start_node, end, t_lookup, budget, not is_white)

	input(f"white: {white}\nblack: {black}\npress enter to start:")
	while True:
		if is_white:
			white.move()
			print(f"white: {white}")
			while True:
				move = input("Move for black: ")
				if (not move.isnumeric()) or all([n != int(move) for n in nodes]):
					print("Node not found."); continue
				if black.move(n_lookup(int(move))):
					print(f"black: {black}"); break

		else:
			while True:
				move = input("Move for white: ")
				if (not move.isnumeric()) or all([n != int(move) for n in nodes]):
					print("Node not found."); continue
				if white.move(n_lookup(int(move))):
					print(f"white: {white}"); break
			black.move()
			print(f"black: {black}")

import json
import sys
from typing import *

import pandas as pd


class InputError(Exception):
	"""problems with the command line input"""


class Node:
	def __init__(self, num: int, critical=False):
		self.num = num
		self.critical = critical
		self.neighbors: List[Tuple["Node", int]] = []

	def __str__(self) -> str:
		return f"{'*' if self.critical else ''}({self.num})"

	def __eq__(self, other: int) -> bool:
		return self.num == other


class Player:
	def __init__(self, budget: int, start: Node):
		self.budget = budget
		self.node = start

	def __str__(self) -> str:
		return f"at {self.node} with budget of {self.budget}"


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
	results = pd.DataFrame(columns=['From', 'To', 'Path', 'Distance', 'Cost'])

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

	try:
		with open(file, "r") as file:
			data = json.load(file)

		locations, roads, start_node, budget = data.values()
		nodes = [Node(n, n in locations["critical"]) for n in list(set(roads["a"] + roads["b"]))]
		for start, end, price in zip(roads["a"], roads["b"], roads["price"]):
			start = nodes[nodes.index(start)]
			end = nodes[nodes.index(end)]
			start.neighbors.append((end, price))
			end.neighbors.append((start, price))
	except:
		raise InputError("input file has the wrong format")

	white = Player(budget, start_node)
	black = Player(budget, start_node)
	you = white if "-white" in sys.argv else black
	print(f"white {white}")
	print(f"white {black}")

	print(dijkstra(nodes, budget))

	# if white:
	#	if white can afford to reach the end:
	#		head towards the end
	#	if not on c_node or black is nearing next c_node in path:  TODO: black is nearing c_node if white can just about win the race towards it
	#		head towards the c_node in path
	#	else: wait on c_node for budget

	# if black:
	#	if black can afford to reach the end:
	#		head towards the end
	#	if not on c_node and black can reach before white:	TODO: white is nearing c_node if black can just about win the race towards it
	#		head towards the c_node in path
	#	elif not on c_node:
	#		look for the fastes alternative path towards the next critical node in the fastest path
	#		if this does not exist walk the best path from current node to end.
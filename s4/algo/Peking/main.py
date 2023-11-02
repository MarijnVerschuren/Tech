import json
import sys


class InputError(Exception):
	"""problems with the command line input"""


class Node:
	def __init__(self, num: int, critical: bool = False):
		self.num = num
		self.critical = critical

	def __str__(self) -> str:				return f"{'*' if self.critical else ''}({self.num})"
	def __eq__(self, other: int) -> bool:	return self.num == other


class Player:
	def __init__(self, budget: int, start: Node):
		self.budget = budget
		self.node = start

	def __str__(self) -> str:	return f"at {self.node} with budget of {self.budget}"



if __name__ == '__main__':
	if "-file" not in sys.argv:					raise InputError("input file not provided")
	if not ("-white" or "-black" in sys.argv):	raise InputError("player not provided")
	file = sys.argv[sys.argv.index("-file") + 1]

	try:
		with open(file, "r") as file:
			data = json.load(file); file.close()
			locations, roads, start_node, budget = data.values()
			nodes = [Node(n, n in locations["critical"]) for n in list(set(roads["a"] + roads["b"]))]
			edges = [(a, roads["b"][i], roads["price"][i]) for i, a in enumerate(roads["a"])]
			start_node = nodes[nodes.index(start_node)]
	except: InputError("input file has the wrong format")

	white = Player(budget, start_node)
	black = Player(budget, start_node)
	you = white if "-white" in sys.argv else black
	print(f"white {white}")
	print(f"white {black}")
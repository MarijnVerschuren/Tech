from typing import *
import random
import time


class node:
	allowed_directions: List[tuple[int, int]] = [
		(-1, -1), (0, -1), (1, -1),
		(-1, 0),           (1, 0),
		(-1, 1),  (0, 1),  (1, 1)
	]
	add = lambda ta, tb: (ta[0] + tb[0], ta[1] + tb[1])

	def __init__(self, position, parent = None):
		self.position = position
		self.parent = parent
		self.g = 0
		self.h = 0
		self.f = 0

	@property
	def x(self) -> int:	return self.position[0]
	@property
	def y(self) -> int:	return self.position[1]
	@property
	def surrounding(self) -> List[Tuple[int, int]]:
		return [node.add(self.position, direction) for direction in self.allowed_directions]
	@property
	def steps(self) -> List["node"]:
		return [node(node.add(self.position, direction), node) for direction in self.allowed_directions]

	def dist(self, other) -> int:		return	(self.position[0] - other.position[0]) ** 2 + \
												(self.position[1] - other.position[1]) ** 2

	def __eq__(self, other) -> bool:	return self.position == other.position
	def __lt__(self, other) -> bool:	return self.f < other.f
	def __gt__(self, other) -> bool:	return self.f > other.f



class maze:
	__CHAR_DEFAULTS = {0: "██", 1: "░░", 2: "▒▒", -1: "xx"}

	@staticmethod
	def identify(data: List[List[int]]) -> Tuple[Tuple[int, int], Tuple[int, int]]:
		start_stop = []
		for y, row in enumerate(data):
			for x, cell in enumerate(row):
				if cell == 2: start_stop.append((x, y))
		if len(start_stop) != 2: return (0, 0), (0, 0)
		return start_stop[0], start_stop[1]


	def __init__(self, data: List[List[int]], chars: Dict[int, str] = None):
		if not chars: chars = maze.__CHAR_DEFAULTS
		self.data = data
		self.start, self.end = maze.identify(data)
		self.chars = chars

	def __getitem__(self, n: node):
		if (lambda x, y: x < 0 or y < 0)(*n.position): return None
		try: return (lambda x, y: self.data[y][x])(*n.position)
		except IndexError: return None

	def __str__(self):
		string = ""
		for row in self.data:
			for cell in row:
				string += self.chars[cell]
			string += "\n"
		return string


class path:
	def __init__(self, m: maze, path: List[Tuple[int, int]]):
		self.path = path
		self.maze = m

	def __str__(self):
		string = ""
		for y, row in enumerate(self.maze.data):
			for x, cell in enumerate(row):
				ip = (x, y) in self.path
				if ip: string += "\033[92m"
				string += self.maze.chars[cell]
				if ip: string += "\033[0m"
			string += "\n"
		return string



def a_star(m: maze) -> path | None:
	open_nodes = [node(m.start)]
	closed_nodes = []
	target = node(m.end)

	current = None
	while open_nodes:
		current = min(open_nodes)
		open_nodes.remove(current)
		closed_nodes.append(current)

		if current == target:
			return path(m, [x.position for x in closed_nodes])

		for child in [child for child in current.steps if child not in closed_nodes and m[child]]:
			child.g = current.g + 1
			child.h = child.dist(target)
			child.f = child.g + child.h

			if child in open_nodes:
				index = open_nodes.index(child)
				if child.g > open_nodes[index].g: continue

			open_nodes.append(child)
	return None


def maze_gen(w: int, h: int) -> maze:
	WALL = 0
	CELL = 1
	ENTRANCE = 2

	directions: Annotated[List[tuple[int, int]], 4] = [
		         (0, -1),
		(-1, 0),          (1, 0),
		         (0, 1)
	]

	maze_data = []
	for _ in range(h):
		row = []
		for __ in range(w):
			row.append(CELL)
		maze_data.append(row)

	stack = []


	m_get = lambda x, y: maze_data[y][x]
	m_set = lambda x, y, z: maze_data[y].__setitem__(x, z)
	t_add = lambda ta, tb: (ta[0] + tb[0], ta[1] + tb[1])

	def validate_node(n: node) -> bool:
		neighboring_walls = 0
		for x, y in n.surrounding:
			if 0 <= x < w and 0 <= y < h and maze_data[y][x] == WALL:
				neighboring_walls += 1
		return (neighboring_walls < 3) and m_get(*n.position) != WALL

	def find_neighbors(n: node) -> List[node]:
		neighbors = []
		positions = [
			(x, y) for x, y in
			[t_add(n.position, direction) for direction in directions]
			if 0 <= x < w and 0 <= y < h
		]
		for pos in positions:
			neighbors.append(node(pos, n))
		return neighbors

	def randomly_add_nodes(nodes: List[node]):
		while len(nodes):
			n = random.choice(nodes)
			nodes.remove(n)
			stack.append(n)


	stack.append(node((0, 0)))
	while len(stack):
		current = stack.pop()
		if validate_node(current):
			m_set(*current.position, WALL)
			neighbors = find_neighbors(current)
			randomly_add_nodes(neighbors)

	m_set(random.randint(0, w-1), random.randint(0, h-1), ENTRANCE)
	m_set(random.randint(0, w-1), random.randint(0, h-1), ENTRANCE)
	#m_set(0, 0, ENTRANCE)
	#m_set(w - 1, h - 1, ENTRANCE)
	return maze(maze_data)



if __name__ == '__main__':
	maze_0 = maze_gen(10, 10)		# 10 * 2^0
	maze_1 = maze_gen(20, 20)		# 10 * 2^1
	maze_2 = maze_gen(40, 40)		# 10 * 2^2
	maze_3 = maze_gen(80, 80)		# 10 * 2^3
	maze_4 = maze_gen(160, 160)	# 10 * 2^4
	maze_5 = maze_gen(320, 320)	# 10 * 2^5

	start = time.time(); sol_0 = a_star(maze_0); time_0 = time.time() - start
	print(f"maze_0 took: {round(time_0, 6)}", sol_0, sep="\n")
	start = time.time(); sol_1 = a_star(maze_1); time_1 = time.time() - start
	print(f"maze_1 took: {round(time_1, 6)},\tdt/dx: {round(time_1 / time_0, 6)}", sol_1, sep="\n")
	start = time.time(); sol_2 = a_star(maze_2); time_2 = time.time() - start
	print(f"maze_2 took: {round(time_2, 6)},\tdt/dx: {round(time_2 / time_1, 6)}", sol_2, sep="\n")
	start = time.time(); sol_3 = a_star(maze_3); time_3 = time.time() - start
	print(f"maze_3 took: {round(time_3, 6)},\tdt/dx: {round(time_3 / time_2, 6)}", sol_3, sep="\n")
	start = time.time(); sol_4 = a_star(maze_4); time_4 = time.time() - start
	print(f"maze_4 took: {round(time_4, 6)},\tdt/dx: {round(time_4 / time_3, 6)}", sol_4, sep="\n")
	start = time.time(); sol_5 = a_star(maze_5); time_5 = time.time() - start
	print(f"maze_5 took: {round(time_5, 6)},\tdt/dx: {round(time_5 / time_4, 6)}", sol_5, sep="\n")


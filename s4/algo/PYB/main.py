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



# BAD CODE!!!
def maze_gen(w: int, h: int) -> maze:  # TODO: improve
	WALL = 0
	CELL = 1
	ENTRANCE = 2
	UNVISITED = -1

	directions: Annotated[List[tuple[int, int]], 4] = [
		         (0, -1),
		(-1, 0),          (1, 0),
		         (0, 1)
	]

	maze_data = []
	for _ in range(h):
		row = []
		for __ in range(w):
			row.append(UNVISITED)  # set all cells as unvisited
		maze_data.append(row)

	m_get = lambda x, y: maze_data[y][x]
	m_set = lambda x, y, z: maze_data[y].__setitem__(x, z)
	t_add = lambda ta, tb: (ta[0] + tb[0], ta[1] + tb[1])

	start = (	# with border of width 1
		random.randint(1, w - 2),
		random.randint(1, h - 2)
	)

	m_set(*start, 0)
	walls = [t_add(start, direction) for direction in directions]
	for wall in walls: m_set(*wall, WALL)

	while (walls):
		rand_wall = random.choice(walls)
		walls.remove(rand_wall)

		cells = [
			((x, y), m_get(x, y)) if 0 < x < w - 1 and 0 < y < h - 1 else (None, None)
			for x, y in [t_add(rand_wall, direction) for direction in directions]
		]

		if len([c for _, c in cells if c is not None and c == CELL]) < 2:
			m_set(*rand_wall, CELL)
			for p, d in cells:
				if p is None or d == CELL: continue
				m_set(*p, WALL)
				if p not in walls: walls.append(p)


	for y in range(h):
		for x in range(w):
			if maze_data[y][x] == UNVISITED:
				maze_data[y][x] = WALL

	for x in range(w):
		if maze_data[1][x] == CELL:
			maze_data[0][x] = ENTRANCE
			break

	for x in range(w - 1, 0, -1):
		if maze_data[h - 2][x] == CELL:
			maze_data[h - 1][x] = ENTRANCE
			break

	return maze(maze_data)
# BAD CODE!!! ^^^


if __name__ == '__main__':
	maze_0 = maze_gen(10, 10)		# 10 * 2^0
	maze_1 = maze_gen(20, 20)		# 10 * 2^1
	maze_2 = maze_gen(40, 40)		# 10 * 2^2
	maze_3 = maze_gen(80, 80)		# 10 * 2^3
	maze_4 = maze_gen(160, 160)	# 10 * 2^4
	maze_5 = maze_gen(320, 320)	# 10 * 2^5

	print("maze generation done")

	start = time.time(); sol_0 = a_star(maze_0); time_0 = time.time() - start
	start = time.time(); sol_1 = a_star(maze_1); time_1 = time.time() - start
	start = time.time(); sol_2 = a_star(maze_2); time_2 = time.time() - start
	start = time.time(); sol_3 = a_star(maze_3); time_3 = time.time() - start
	start = time.time(); sol_4 = a_star(maze_4); time_4 = time.time() - start
	start = time.time(); sol_5 = a_star(maze_5); time_5 = time.time() - start

	print(f"maze_0 took: {round(time_0, 6)}")
	print(f"maze_1 took: {round(time_1, 6)},\tdt/dx: {round(time_1 / time_0, 6)}")
	print(f"maze_2 took: {round(time_2, 6)},\tdt/dx: {round(time_2 / time_1, 6)}")
	print(f"maze_3 took: {round(time_3, 6)},\tdt/dx: {round(time_3 / time_2, 6)}")
	print(f"maze_4 took: {round(time_4, 6)},\tdt/dx: {round(time_4 / time_3, 6)}")
	print(f"maze_5 took: {round(time_5, 6)},\tdt/dx: {round(time_5 / time_4, 6)}")

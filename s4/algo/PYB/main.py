from typing import *


# test data TODO: make a noise generator library
test_maze = [
	[2, 1, 1, 1, 0, 1, 1, 1, 2],
	[0, 0, 0, 1, 0, 1, 0, 0, 0],
	[0, 0, 0, 1, 1, 1, 0, 0, 0]
]
start_stop = []
for y, row in enumerate(test_maze):
	for x, cell in enumerate(row):
		if cell == 2: start_stop.append((x, y))



class node:
	def __init__(self, position, parent = None):
		self.position = position
		self.parent = parent
		self.g = 0
		self.h = 0
		self.f = 0

	def __eq__(self, other) -> bool:	return self.position == other.position
	def __lt__(self, other) -> bool:	return self.f < other.f
	def __gt__(self, other) -> bool:	return self.f > other.f


def a_star(
		start: tuple[int, int], target: tuple[int, int],
		maze: list[list[int]], allowed_directions: tuple[tuple[int, int]] = (
			(-1, -1), (0, -1), (1, -1),
			(-1, 0),           (1, 0),
			(-1, 1),  (0, 1),  (1, 1)
		)
) -> list[tuple[int, int]]:
	open_nodes = [node(start)]
	closed_nodes = []
	target = node(target)

	index = lambda x, y: maze[y][x] if maze[y:] and maze[x:] else None
	add = lambda ta, tb: (ta[0] + tb[0], ta[1] + tb[1])
	sub = lambda ta, tb: (ta[0] - tb[0], ta[1] - tb[1])

	current = None
	while open_nodes:
		current = min(open_nodes)
		open_nodes.remove(current)
		closed_nodes.append(current)

		if current == target:
			return [(0, 0)] # TODO: construct path

		for direction in allowed_directions:
			position = add(current.position, direction)
			if index(*position): continue
			child = node(
				position,
				current
			)
			if child in closed_nodes: continue

			distance = sub(child.position, target.position)
			child.g = current.g + 1
			child.h = (distance[0] ** 2) + (distance[1] ** 2)
			child.f = child.g + child.h

			if index := open_nodes.index(child):
				if child.g > open_nodes[index].g: continue



if __name__ == '__main__':
	a_star(*start_stop, test_maze)

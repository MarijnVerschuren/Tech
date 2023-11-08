from z3 import *

GRID_SIZE = 6
GEN_COUNT = 10
solver = Solver()


grid = [
	[
		[Bool("c_%s_%s_%s" % (gen, y, x)) for x in range(GRID_SIZE)]
		for y in range(GRID_SIZE)
	]
	for gen in range(GEN_COUNT)
]

for y in range(GRID_SIZE):
	for x in range(GRID_SIZE):
		for gen in range(1, GEN_COUNT):
			alive_neighbors = sum(
				[
					If(grid[gen - 1][(y + j) % GRID_SIZE][(x + i) % GRID_SIZE], 1, 0)
					for i in [-1, 0, 1]
					for j in [-1, 0, 1]
					if (i != j and i == 0)
				]
			)
			grid[gen - 1][y][x] = If(
				grid[gen - 1][y][x],
				Or(
					alive_neighbors == 2,
					alive_neighbors == 3
				),
				alive_neighbors == 3
			)

for y in range(GRID_SIZE):
	for x in range(GRID_SIZE):
		for gen in range(GEN_COUNT):
			grid[gen][y][x] = Or(
				*[
					And(
						(Not(grid[g + 1][y][x]),
						grid[g + 2][y][x])
					)
					for g in range(gen, GEN_COUNT - 2)
					if gen < GEN_COUNT - 2
				],
				*[
					And(
						(Not(grid[g + 1][y][x]),
						(Not(grid[g + 2][y][x])),
						(Not(grid[g + 3][y][x])),
						grid[g + 4][y][x])
					)
					for g in range(gen, GEN_COUNT - 4)
					if gen < GEN_COUNT - 4
				]
			)


result = solver.check()

if __name__ == "__main__":
	print_matrix(grid)

	if result == sat:
		model = solver.model()
		for gen in range(GEN_COUNT):
			print(f"Generation {gen}:")
			for y in range(GRID_SIZE):
				for x in range(GRID_SIZE):
					cell = grid[gen][y][x]
					if is_true(cell): print("1", end=" ")
					else: print("0", end=" ")
				print()
			print()
	else:
		print("No solution found.")

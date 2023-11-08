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

# Define an initial configuration (customize as needed)
initial_config = [
    (2, 2), (2, 3), (2, 4),
    (3, 1), (3, 2), (3, 3)
]

# Set the initial configuration to live cells
for x, y in initial_config:
    grid[0][y][x] = True

for gen in range(1, GEN_COUNT):
    for y in range(GRID_SIZE):
        for x in range(GRID_SIZE):
            # Add rules for cell state changes
            alive_neighbors = sum(
                [
                    If(grid[gen - 1][(y + j) % GRID_SIZE][(x + i) % GRID_SIZE], 1, 0)
                    for i in [-1, 0, 1]
                    for j in [-1, 0, 1]
                    if (i != 0 or j != 0)
                ]
            )

            cell = grid[gen - 1][y][x]
            cell_next = If(
                And(cell, Or(alive_neighbors == 2, alive_neighbors == 3)),
                True,
                If(And(Not(cell), alive_neighbors == 3), True, False)
            )

            # Add the rule to the solver
            solver.add(grid[gen][y][x] == cell_next)

result = solver.check()

if result == sat:
    model = solver.model()
    for gen in range(GEN_COUNT):
        print(f"Generation {gen}:")
        for y in range(GRID_SIZE):
            for x in range(GRID_SIZE):
                cell = grid[gen][y][x]
                if is_true(cell):
                    print("1", end=" ")
                else:
                    print("0", end=" ")
            print()
        print()
else:
    print("No solution found.")

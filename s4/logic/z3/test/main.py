import z3-solver


ctx = z3.Context()
solver = z3.Solver(ctx=ctx)
solver.set("model.completion", True)
x = z3.Bool("x", ctx)
y = z3.Bool("y", ctx)
z = z3.Bool("z", ctx)
solver.add(z3.Or([x, y, z]))

while True:
    result = solver.check()
    if result == z3.unsat:
        break
    m = solver.model()
    assert m[x] is not None and m[y] is not None
    solver.add(z3.Or([x != m[x], y != m[y]]))

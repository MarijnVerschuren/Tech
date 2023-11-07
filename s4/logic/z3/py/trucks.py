from z3 import *


solver = Solver()


truck = Datatype("truck")
for t in ("truck_1", "truck_2", "truck_3", "truck_4", "truck_5", "truck_6"):
	truck.declare(t)
truck = truck.create()

pallet = Datatype("pallet")
for p in ("nuzzles", "prittles", "skipples", "crottles", "dupples"):
	pallet.declare(p)
pallet = pallet.create()

count = Function("count", IntSort(), IntSort())


solver.add(
	ForAll(
		[truck],
		And(
			(
				800 * count(t, pallet.nuzzles) +
				1300 * count(t, pallet.prittles)
			) <= 8000,
			(
				count(t, pallet.nuzzles) +
				count(t, pallet.prittles)
			) <= 8,
			ForAll(
				[pallet],
				count(truck, p) >= 0
			)
		)
	)
)

print(solver.check())
print(solver.model())

out = """
((grid 0 0 0) false)
((grid 1 0 0) false)
((grid 2 0 0) false)
((grid 3 0 0) false)
((grid 4 0 0) false)
((grid 5 0 0) true)
((grid 0 1 0) false)
((grid 1 1 0) false)
((grid 2 1 0) true)
((grid 3 1 0) true)
((grid 4 1 0) true)
((grid 5 1 0) false)
((grid 0 2 0) false)
((grid 1 2 0) false)
((grid 2 2 0) true)
((grid 3 2 0) true)
((grid 4 2 0) false)
((grid 5 2 0) true)
((grid 0 3 0) false)
((grid 1 3 0) true)
((grid 2 3 0) false)
((grid 3 3 0) false)
((grid 4 3 0) true)
((grid 5 3 0) true)
((grid 0 4 0) true)
((grid 1 4 0) false)
((grid 2 4 0) false)
((grid 3 4 0) false)
((grid 4 4 0) false)
((grid 5 4 0) true)
((grid 0 5 0) false)
((grid 1 5 0) false)
((grid 2 5 0) true)
((grid 3 5 0) false)
((grid 4 5 0) false)
((grid 5 5 0) true)
"""

dat = out.split("\n")
arr = [
	[0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0]
]

for d in dat:
	if not d: continue
	d = d.replace("((grid ", "")
	pos, val = d.split(") ")
	val = val.replace(")", "") == "true"
	x, y, _ = pos.split(" ")
	x = int(x); y = int(y)
	arr[y][x] = val

for row in arr:
	for cell in row:
		print("1" if cell else "0", end=" ")
	print()

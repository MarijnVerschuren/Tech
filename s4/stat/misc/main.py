import numpy as np
import matplotlib.pyplot as plt
import json


choices = {
	"a": [0, 1],
	"p": [0.5, 0.5],
}
chain_length = 10

if __name__ == "__main__":
	sums = [0] * chain_length
	rnds = []
	for _ in range(1000):
		rnd = [np.random.choice(**choices) for __ in range(chain_length)]
		rnds.append(rnd)
		sums[sum(rnd) - 1] += 1

	# | A0/x | 0 | 1 |
	# +------+-------|
	# | 0    |
	# | 1    |
	# | ...  |
	# | x    |
	stats = []
	for i in range(1, chain_length):
		table = []
		for _ in range(i + 2):
			table.append([0, 0])
		stats.append(table)

	for rnd in rnds:
		for i in range(1, chain_length):
			stats[i - 1][sum(rnd[:i + 1])][rnd[0]] += 1

	for table in stats:
		for row in table:
			print(row)
		print()


	fig, ax = plt.subplots()
	ax.bar(range(chain_length), sums)
	plt.show()


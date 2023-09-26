from typing import List


# input helper
def remove(x: str, *args: str) -> str:
	for arg in args:
		x.replace(arg, "")
	return x


# merge sort functions
def merge(x: List[int], y: List[int]) -> List[int]:
	if len(x) and not len(y):   return x
	if len(y) and not len(x):   return y
	if x[0] < y[0]:             return [x[0]] + merge(x[1:], y)
	else:                       return [y[0]] + merge(x, y[1:])
	

def merge_sort(x: List[int]) -> List[int]:
	if len(x) < 2: return x
	return merge(
		merge_sort(x[:len(x)//2]),
		merge_sort(x[len(x)//2:])
	)


# entry point
if __name__ == "__main__":
	elements = [int(element) for element in remove(input("elements : int > "), " ", "\n", "\t").split(",")]
	print(elements, merge_sort(elements))

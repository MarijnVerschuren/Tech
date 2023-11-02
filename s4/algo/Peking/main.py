import json
from functools import cache
import sys

import pandas as pd


class InputError(Exception):
    """problems with the command line input"""


class Node:
    def __init__(self, num: int, neighbors: list[tuple["Node", int]], critical=False):
        self.num = num
        self.critical = critical
        self.neighbors = neighbors  # To: cost

    def __str__(self) -> str:
        return f"{'*' if self.critical else ''}({self.num})"

    def __eq__(self, other: int) -> bool:
        return self.num == other


class Player:
    def __init__(self, budget: int, start: Node):
        self.budget = budget
        self.node = start

    def __str__(self) -> str:
        return f"at {self.node} with budget of {self.budget}"


def GetEntirePath(fromNodeNum: int, shortestPaths: dict[int, tuple[Node, int]]) -> list[Node]:
    if fromNodeNum not in shortestPaths:
        return []

    if shortestPaths[fromNodeNum][0] == fromNodeNum:  # At start node
        return [GetNode(nodes, fromNodeNum)]

    if not shortestPaths[fromNodeNum][0]:
        return []

    if path := GetEntirePath(shortestPaths[fromNodeNum][0].num, shortestPaths):
        return path + [GetNode(nodes, fromNodeNum)]

    return []


def GetNode(nodes: list[Node], num: int) -> Node:
    for node in nodes:
        if node.num == num:
            return node
    else:
        raise Exception(f"Node not found, num: {num}")


# Dijkstra
#   Critical locations
#   Budget
def GetShortestFromNode(nodes: list[Node], start: Node) -> dict[int, tuple[Node, int]]:  # Result: O((M+1)N)
    shortestPaths = {node.num: (None, float('inf')) for node in nodes}  # Node: (from, cost). O(N)
    shortestPaths[start.num] = (start.num, 0)

    queue = [start]

    while queue:  # Result: O(MN)
        currentNode = queue.pop(0)  # O(N), since all elements have to be shifted.

        for neighborNum, cost in currentNode.neighbors:  # O(M)
            newDist = shortestPaths[currentNode.num][1] + cost

            if newDist < shortestPaths[neighborNum][1]:
                shortestPaths[neighborNum] = (currentNode, newDist)
                queue.append(GetNode(nodes, neighborNum))

    return shortestPaths


def DijkstraPlus(nodes: list[Node]) -> pd.DataFrame:  # Result: O((M+2)N)
    results = pd.DataFrame(columns=['From', 'To', 'Path', 'Cost'])

    for start in nodes:
        shortestPaths = GetShortestFromNode(nodes, start)  # O((M+1)N)

        for node, (fromNode, cost) in shortestPaths.items():  # O(N)
            results.loc[len(results.index)] = [start.num, node, GetEntirePath(node, shortestPaths), cost]

    return results


def GetNeighbors(roads: dict[str, int], node: int) -> list[tuple[str, int]]:
    return [(to, price) for start, to, price in zip(roads["a"], roads["b"], roads["price"]) if node == start] + \
           [(start, price) for start, to, price in zip(roads["a"], roads["b"], roads["price"]) if node == to]


if __name__ == '__main__':
    if "-file" not in sys.argv:
        raise InputError("input file not provided")
    if not ("-white" or "-black" in sys.argv):
        raise InputError("player not provided")
    file = sys.argv[sys.argv.index("-file") + 1]

    try:
        with open(file, "r") as file:
            data = json.load(file)

        locations, roads, start_node, budget = data.values()
        nodes = [Node(n,
                      GetNeighbors(roads, n),
                      n in locations["critical"]) for n in list(set(roads["a"] + roads["b"]))]
        # edges = [(a, roads["b"][i], roads["price"][i]) for i, a in enumerate(roads["a"])]
    except:
        raise InputError("input file has the wrong format")

    white = Player(budget, start_node)
    black = Player(budget, start_node)
    you = white if "-white" in sys.argv else black
    print(f"white {white}")
    print(f"white {black}")

    print(DijkstraPlus(nodes))  # O((M+2)N)

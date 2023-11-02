import json
from functools import cache
import sys


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


def GetEntirePath(fromNode: Node, shortestPaths: dict[Node, tuple[Node, int]]) -> list[Node]:
    if fromNode not in shortestPaths:
        return []

    if shortestPaths[fromNode][0] == fromNode:  # At start node
        return [fromNode]

    if path := GetEntirePath(shortestPaths[fromNode][0], shortestPaths):
        return path + [fromNode]

    return []


# Dijkstra
#   Critical locations
#   Budget
@cache
def GetShortestFromNode(nodes: list[Node], start: Node, end: Node) -> dict[Node, tuple[Node, int]]:  # Result: O((M+1)N)
    shortestPaths = {node: (None, float('inf')) for node in nodes}  # Node: (from, dist). O(N)
    shortestPaths[start] = (start, 0)

    queue = [start]

    while queue:  # Result: O(MN)
        currentNode = queue.pop(0)  # O(N), since all elements have to be shifted.

        for neighbor, dist in shortestPaths[currentNode].items():  # O(M)
            newDist = shortestPaths[currentNode][1] + dist

            if newDist < shortestPaths[neighbor][1]:
                shortestPaths[neighbor] = (currentNode, newDist)
                queue.append(neighbor)

                if neighbor == end:
                    return shortestPaths

    return shortestPaths


def Dijkstra(nodes: list[Node], start: Node, end: Node) -> tuple[list[Node], int]:  # Result: O((M+2)N)
    shortestPaths = GetShortestFromNode(nodes, start, end)  # O((M+1)N)

    fromNode, dist = shortestPaths[end]
    return GetEntirePath(end, shortestPaths), dist


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
                      {to: price for start, to, price in zip(roads["a"], roads["b"], roads["price"]) if start is n},
                      n in locations["critical"]) for n in list(set(roads["a"] + roads["b"]))]
        edges = [(a, roads["b"][i], roads["price"][i]) for i, a in enumerate(roads["a"])]
        start_node = nodes[nodes.index(start_node)]
        end_node = nodes[-1]  # Just picking a random one for now.
    except:
        raise InputError("input file has the wrong format")

    white = Player(budget, start_node)
    black = Player(budget, start_node)
    you = white if "-white" in sys.argv else black
    print(f"white {white}")
    print(f"white {black}")

    print(Dijkstra(nodes, start_node, end_node))  # O((M+2)N)

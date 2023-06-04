#include <iostream>

#include "graph.hpp"


int main() {
	Graph<uint64_t>* graph = new Graph<uint64_t>(0);
	Graph<uint64_t>* branch;
	Path<uint64_t>* path;
	branch = graph->add(1);
	branch->add(5);
	branch->add(6);
	branch = graph->add(2);
	graph->add(branch->add(4));
	graph->add(3);

	// TODO: auto link nodes when node is already present in tree (may not be needed!!)
	// TODO: keep track of checked nodes so that no infinite loops can be created
	// TODO: cin

	print(graph);
	path = DFS<uint64_t>(graph, 4ul); print(path);
	path = BFS<uint64_t>(graph, 4ul); print(path);

	return 0;
}

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>

#include "graph.hpp"


int main() {
	Graph<uint64_t>* graph = new Graph<uint64_t>(1);
	Graph<uint64_t> *a, *b, *c, *d;
	Path<uint64_t>* path;
	a = graph->add(2);
	b = a->add(3);
	c = b->add(4);
	c->add(a);
	graph->add(b);

	// TODO: auto link nodes when node is already present in tree (may not be needed!!)
	// TODO: keep track of checked nodes so that no infinite loops can be created
	// TODO: cin

	print(graph);
	debug_print(graph);
	std::cout << "depth: " << graph->depth() << "\n";

	//path = DFS<uint64_t>(graph, 4ul); print(path);
	path = BFS<uint64_t>(graph, 3ul); print(path);

	return 0;
}

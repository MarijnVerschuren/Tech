#include <iostream>
#include <vector>
#include <stdint.h>
#include <list>

#include "graph.hpp"
using namespace std;


int main() {
	uint64_t t, n, m, x, y;

	cin >> t;  // 't' tests
	for(uint64_t i = 0; i < t; i++) {
		cin >> n >> m;  // 'n' nodes, 'm' inputs
		vector<vector<uint64_t>>	neighbors(n);
		vector<bool>				visited(n);
		list<uint64_t>	queue;
		for (uint64_t j = 0; j < n; j++) { visited[j] = false; }
		for (uint64_t j = 0; j < m; j++) {
			cin >> x >> y;  // 'x' connected to 'y'
			neighbors[x-1].push_back(y-1);
			neighbors[y-1].push_back(x-1);
		}
		// 'visit' first node
		queue.push_back(0);
		visited[0] = true;
		// BFS traverse
		while (!queue.empty()) {
			uint64_t current = queue.front();
			queue.pop_front();
			std::cout << "visit: " << current << "\n";
			for (uint64_t neighbor : neighbors[current]) {
				queue.push_back(neighbor);
				visited[neighbor] = true;
			}
		}
	}

	return 0;
	/*
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
	*/
}

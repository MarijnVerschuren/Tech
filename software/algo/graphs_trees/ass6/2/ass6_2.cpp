#include <iostream>
#include <string.h>

#include "graph.hpp"


using namespace std;


int main(){
	uint64_t t, n, m, x, y;
	uint64_t route_count;
	Graph<uint64_t>* graphs[100000];  // 10^5 max nodes

    cin >> t;
    for(uint64_t i = 0; i < t; i++) {
		cin >> n >> m;
		for (uint64_t j = 0; j < m + 1; j++) { graphs[j] = new Graph<uint64_t>(j + 1); }
		for (uint64_t j = 0; j < m; j++) {
			cin >> x >> y;
			graphs[x - 1]->add(graphs[y - 1]);
		}
		Path<uint64_t>* path = BFS(graphs[0], n);
		if (!path) { cout << "not found\n"; continue; }
		route_count = path->step_count();
		cout << route_count << " ";
		print(path);
		delete graphs[0];
    }

    return 0;
}
// FKIN seg fault on depth func
// TODO: fix cyclic references
#include <iostream>
#include <string.h>

#include "graph.hpp"


using namespace std;

int main(){
	uint64_t t, n, m, x, y;
	uint64_t route_count;
	Graph<uint64_t>* graphs[100000];  // 10^5 max nodes
	set_max_graph_nodes(100000);

    cin >> t;
    for(uint64_t i = 0; i < t; i++) {
		cout << "t: " << i << "\n";
		cin >> n >> m;
		for (uint64_t j = 0; j < m + 1; j++) { graphs[j] = new Graph<uint64_t>(j + 1); }
		for (uint64_t j = 0; j < m; j++) {
			cin >> x >> y;
			if (i == 1) { cout << x << ", " << y << " -> "; }
			if (i == 1) { cout << graphs[x - 1]->get_data() << ", " << graphs[y - 1]->get_data(); }
			graphs[x - 1]->add(graphs[y - 1]);
			if (i == 1) { cout << " added\n"; }
		}
		//if (i == 1) { debug_print(graphs[0]); }
		cout << graphs[0]->depth() << "\n";
		if (i == 1) { for(;;); }
		Path<uint64_t>* path = BFS(graphs[0], n);
		delete graphs[0];
		memset(graphs, 0x0, sizeof(graphs));
		if (!path) { continue; }
		route_count = path->step_count();
        cout << route_count << endl;
		if (i == 1) { for(;;); }
    }

    return 0;

}
// FKIN seg fault on depth func
// TODO: fix cyclic references
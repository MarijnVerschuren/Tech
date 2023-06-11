#include <iostream>

#include "graph.hpp"


using namespace std;

int main()
{
	uint64_t n;
	cin >> n;

	Graph<uint64_t>** graphs = new Graph<uint64_t>*[n]();
	for(uint64_t i = 0; i < n; i++) { graphs[i] = new Graph<uint64_t>(i + 1); }  // create all nodes first
	for(uint64_t i = 0; i < n; i++) {
		uint64_t nr, left, right;
		cin >> nr >> left >> right;
		if (left) { graphs[nr - 1]->add(graphs[left - 1]); }
		if (right) { graphs[nr - 1]->add(graphs[right - 1]); }
	}
	uint64_t depth = graphs[0]->depth();
	cout << "depth is " << depth << endl;
	return 0;
}

// DONE
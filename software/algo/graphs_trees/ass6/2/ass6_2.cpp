#include <iostream>
#include <vector>
#include <stdint.h>
#include <list>

using namespace std;

struct queue_item {
	uint64_t node;
	uint64_t level;
};


int main(){
	uint64_t t, n, m, x, y;

	cin >> t;  // 't' tests
	for(uint64_t i = 0; i < t; i++) {
		cin >> n >> m;  // 'n' nodes, 'm' inputs
		vector<vector<uint64_t>>	neighbors(n);
		vector<bool>				visited(n);
		list<queue_item>			queue;
		for (uint64_t j = 0; j < n; j++) { visited[j] = false; }
		for (uint64_t j = 0; j < m; j++) {
			cin >> x >> y;  // 'x' connected to 'y'
			neighbors[x-1].push_back(y-1);
			neighbors[y-1].push_back(x-1);
		}
		// 'visit' first node
		queue.push_back({0, 0});
		visited[0] = true;
		// BFS traverse
		while (!queue.empty()) {
			queue_item current = queue.front();
			if (current.node == (n-1)) { std::cout << current.level << "\n"; }
			queue.pop_front();
			for (uint64_t neighbor : neighbors[current.node]) {
				if (visited[neighbor]) { continue; }
				queue.push_back({neighbor, current.level + 1});
				visited[neighbor] = true;
			}
		}
	}

	return 0;
}
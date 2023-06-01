#include <iostream>

#include "tree.hpp"


int main() {
	Tree<uint64_t>* tree = new Tree<uint64_t>(0);
	Tree<uint64_t>* branch;
	Tree_Path<uint64_t>* path;
	branch = tree->add(1);
	branch->add(5);
	branch->add(6);
	branch = tree->add(2);
	branch->add(4);
	tree->add(3);
	tree->add(4);  // TODO: linking

	print(tree);
	path = DFS<uint64_t>(tree, 4ul); print(path);
	path = BFS<uint64_t>(tree, 4ul);
	print(path);

	return 0;
}

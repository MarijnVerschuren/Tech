#include <iostream>

#include "tree.hpp"


int main() {
	auto tree = new Tree<uint64_t>(0);
	tree->add(1);
	auto branch = tree->add(2);
	branch->add(4);
	tree->add(3);

	print(tree);
	const Tree_Path<uint64_t>* path = DFS(tree, 0ul);
	print(path);

	return 0;
}

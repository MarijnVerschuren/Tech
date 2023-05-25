//
// Created by marijn on 5/25/23.
//
#ifndef PROJECT_BINARY_TREE_H
#define PROJECT_BINARY_TREE_H
#include <cstdint>
#include <vector>


template<typename type>
class Tree;
template<typename type>
class Tree_Path;

template<typename type>
void print(const Tree<type>*, const std::string& = "");


template<typename type>
class Tree_Path {  // this class holds a constant path inside a tree
private:
	Tree<type>*				tree = nullptr;
	std::vector<uint64_t>	path;  // array of child indices

	explicit Tree_Path(Tree<type>* tree)	{ this->tree = tree; }
	void add(uint64_t step)					{ this->path.push_back(step); }
	void set(uint64_t index, uint64_t step)	{ this->path[index] = step; }

public:
	Tree_Path() = delete;  // path may not be created outside the context of a tree search algorithm

	uint64_t step_count() const				{ return this->path.size(); }
	const Tree<type>* traverse() const {
		Tree<type>* tree = this->tree;
		for (uint64_t step : this->path) {
			if (!tree) { return (Tree<type>*)nullptr; }
			tree = tree->get_child(step);
		} return tree;
	}

	friend Tree_Path<type>* Tree<type>::DFS(type);
	friend Tree_Path<type>* Tree<type>::BFS(type);
	friend Tree_Path<type>* Tree<type>::PDFS(type);
	friend Tree_Path<type>* Tree<type>::PBFS(type);
	friend Tree_Path<type>* Tree<type>::dijkstra_search(type);
};


template<typename type>
class Tree {
private:
	Tree<type>* parent = nullptr;
	std::vector<Tree<type>*> children;
	std::vector<Tree<type>*> siblings;
	type data;
public:
	explicit Tree(type data) { this->data = data; }
	explicit Tree(Tree<type>* parent, type data) {
		this->parent = parent;
		this->data = data;
	}
	~Tree() { for (auto child : this->children) 	{ delete child; } }

	void add(Tree<type>* new_child) {
		for (auto child : this->children) {
			new_child->add_sibling(child);
			child->add_sibling(new_child);
		}
		this->children.push_back(new_child);
	}
	Tree<type>* add(type data) {
		Tree<type>* new_child = new Tree<type>(this, data);
		this->add(new_child); return new_child;
	}
	void add_sibling(Tree<type>* sibling)			{ this->siblings.push_back(sibling); }
	Tree<type>* add_sibling(type data)				{ return this->parent->add(data); }

	uint64_t child_count() const					{ return this->children.size(); }
	uint64_t sibling_count() const					{ return this->siblings.size(); }
	Tree<type>* get_child(uint64_t index) const		{ return this->children[index]; }
	Tree<type>* get_sibling(uint64_t index)	const	{ return this->siblings[index]; }
	Tree<type>* get_parent() const					{ return this->parent; }
	type get_data() const							{ return this->data; }
	uint64_t depth() const							{ uint64_t depth; this->depth(&depth); return depth; }
	Tree<type>* depth(uint64_t* const depth) const {
		Tree<type>* deepest_child = nullptr;
		(*depth) = 0; uint64_t child_depth;
		for (auto child : this->children) {
			child_depth = child->depth();
			if (child_depth > (*depth)) {
				(*depth) = child_depth;
				deepest_child = child;
			}
		} (*depth)++;  // add own depth
		return deepest_child;
	}

	Tree_Path<type>* DFS(type data) {
		Tree_Path<type>* path = new Tree_Path<type>(this);
		return path;
	}
	Tree_Path<type>* BFS(type data) {
		Tree_Path<type>* path = new Tree_Path<type>(this);
		return path;
	}
	Tree_Path<type>* PDFS(type data) {
		Tree_Path<type>* path = new Tree_Path<type>(this);
		return path;
	}
	Tree_Path<type>* PBFS(type data) {
		Tree_Path<type>* path = new Tree_Path<type>(this);
		return path;
	}
	Tree_Path<type>* dijkstra_search(type data) {
		Tree_Path<type>* path = new Tree_Path<type>(this);
		return path;
	}

	friend void print<type>(const Tree<type>*, const std::string&);
};


template<typename type>
void print(const Tree<type>* tree, const std::string& before) {
	std::cout << before << " - (" << tree->data << ")\n";
	const std::string indent = before + " |";
	for (auto child : tree->children) { print<type>(child, indent); }
	if (before.empty()) { std::cout << "\n\n"; }  // root
}

#endif //PROJECT_BINARY_TREE_H

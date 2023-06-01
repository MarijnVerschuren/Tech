//
// Created by marijn on 5/25/23.
//
#ifndef PROJECT_BINARY_TREE_H
#define PROJECT_BINARY_TREE_H
#include <cstdint>
#include <vector>


/* definitions */
template<typename type>	class Tree;
template<typename type>	class Tree_Path;

template<typename type>	void print(const Tree<type>*, const std::string& = "");
template<typename type>	void print(const Tree_Path<type>*);
template<typename type> Tree_Path<type>* DFS(const Tree<type>*, type, Tree_Path<type>* = nullptr);
template<typename type> Tree_Path<type>* BFS(const Tree<type>*, type, Tree_Path<type>* = nullptr, const Tree<type>* = nullptr);


/* classes */
template<typename type>
class Tree {
private:
	std::vector<Tree<type>*> parents;
	std::vector<Tree<type>*> children;
	type data;
public:
	explicit Tree(type data) { this->data = data; }
	explicit Tree(Tree<type>* parent, type data) {
		this->parents.push_back(parent);
		this->data = data;
	}
	~Tree() { for (auto child : this->children) 	{ delete child; } }

	void add_parent(Tree<type>* parent) {
		this->parents.push_back(parent);
	}
	void add(Tree<type>* new_child) {
		new_child->add_parent(this);
		this->children.push_back(new_child);
	}
	Tree<type>* add(type data) {
		Tree<type>* new_child = new Tree<type>(this, data);
		this->add(new_child); return new_child;
	}

	uint64_t parent_count() const						{ return this->parents.size(); }
	uint64_t child_count() const						{ return this->children.size(); }
	Tree<type>* get_child(uint64_t index) const			{ return this->children[index]; }
	Tree<type>* get_parent(uint64_t index) const		{ return this->parents[index]; }

	type get_data() const								{ return this->data; }
	uint64_t depth() const								{ uint64_t depth; this->depth(&depth); return depth; }
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

	// TODO: node removal


	friend void print<type>(const Tree<type>*, const std::string&);
	friend void print<type>(const Tree_Path<type>*);

	friend Tree_Path<type>* DFS<type>(const Tree<type>*, type, Tree_Path<type>*);
	friend Tree_Path<type>* BFS<type>(const Tree<type>*, type, Tree_Path<type>*, const Tree<type>*);
};


template<typename type>
class Tree_Path {  // this class holds a constant path inside a tree
private:
	const Tree<type>*		tree = nullptr;
	std::vector<uint64_t>	path;  // array of child indices

	explicit Tree_Path(const Tree<type>* tree)				{ this->tree = tree; }
	void push(uint64_t step)								{ this->path.push_back(step); }
	void reserve() /* expand the step vector */				{ this->path.push_back(-1); }
	void claim(uint64_t step) /* claim reserved space */	{ this->set(this->path.size() - 1, step); }
	void set(uint64_t index, uint64_t step)					{ this->path[index] = step; }
	void pop()												{ this->path.pop_back(); }

public:
	Tree_Path() = delete;  // Tree_Path instance may not be created outside the context of a tree search algorithm though you may copy it
	Tree_Path(Tree_Path& path) {
		this->tree = path.tree;
		for (auto step : path.path) { this->path.push_back(step); }
	}
	// tree is NOT deleted when deleting path

	uint64_t step_count() const					{ return this->path.size(); }
	const uint64_t* steps(uint64_t* size) const { (*size) = this->path.size(); return &this->path[0]; }
	const Tree<type>* traverse() const {
		Tree<type>* tree = this->tree;
		for (uint64_t step : this->path) {
			if (!tree) { return (Tree<type>*)nullptr; }
			tree = tree->get_child(step);
		} return tree;
	}


	friend void print<type>(const Tree_Path<type>*);

	friend Tree_Path<type>* DFS<type>(const Tree<type>*, type, Tree_Path<type>*);
	friend Tree_Path<type>* BFS<type>(const Tree<type>*, type, Tree_Path<type>*, const Tree<type>*);
};


/* friend functions */
template<typename type>
void print(const Tree<type>* tree, const std::string& before) {
	std::cout << before << " - (" << tree->data << ")\n";
	const std::string indent = before + " |";
	for (auto child : tree->children) { print(child, indent); }
	if (before.empty()) { std::cout << "\n\n"; }  // root
}

template<typename type>
void print(const Tree_Path<type>* path) {
	if (!path) { return; }
	const Tree<type>* tree = path->tree;
	std::cout << "(" << tree->data << ")";
	for (uint64_t step : path->path) {
		tree = tree->get_child(step);
		std::cout << " -> (" << tree->data << ")";
	} std::cout << "\n";
}

template<typename type>
Tree_Path<type>* DFS(const Tree<type>* tree, type data, Tree_Path<type>* path) {
	if (!tree) { return nullptr; }
	bool root = !path; if (root) { path = new Tree_Path<type>(tree); }
	if (tree->data == data) { return path; }
	path->reserve();  // add temporary entry which will be claimed
	Tree<type>* child;  // loop variable for the tree children
	Tree_Path<type>* final_path;  // returned path to data
	for (uint64_t i = 0; i < tree->child_count(); i++) {
		child = tree->get_child(i);
		if (!child) { return nullptr; }  // error
		path->claim(i);
		if (child->data == data) { return path; }
		final_path = DFS(child, data, path);
		if (final_path) { return final_path; }
	}
	if (root) { delete path; }  // failed to construct successful path
	else { path->pop(); }  // pop end of path because it holds a temporary step
	return nullptr;  // not found
}
template<typename type>
Tree_Path<type>* BFS(const Tree<type>* tree, type data, Tree_Path<type>* path, const Tree<type>* parent) {
	if (!tree) { return nullptr; }
	bool root = !path; if (root) { path = new Tree_Path<type>(tree); }
	if (tree->data == data) { return path; }
	if (parent) {
		Tree<type>* sibling;  // loop variable for the siblings
		for (uint64_t i = 0; i < parent->child_count(); i++) {
			sibling = parent->get_child(i);
			if (!sibling) { return nullptr; }  // error
			if (sibling->data == data) {
				path->claim(i);
				return path;
			}
		}
	}
	Tree<type>* child;  // loop variable for the tree children
	Tree_Path<type>* final_path;  // returned path to data
	path->reserve();  // add temporary entry which will be claimed
	for (uint64_t i = 0; i < tree->child_count(); i++) {
		child = tree->get_child(i);
		if (!child) { return nullptr; }  // error
		path->claim(i);
		final_path = BFS(child, data, path, tree);
		if (final_path) { return final_path; }
	}
	path->pop();
	if (root) { delete path; }  // failed to construct successful path
	return nullptr;  // not found
}


#endif //PROJECT_BINARY_TREE_H

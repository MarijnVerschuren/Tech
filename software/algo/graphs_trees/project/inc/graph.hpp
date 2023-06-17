//
// Created by marijn on 5/25/23.
//
#ifndef PROJECT_GRAPH_H
#define PROJECT_GRAPH_H
#include <iostream>
#include <cstdint>
#include <vector>
#include <string.h>


/* definitions */
template<typename type>	class Graph;
template<typename type>	class Path;

template<typename type>	void print(Graph<type>*, const std::string& = "");
template<typename type> void debug_print(Graph<type>*, const std::string& = "");
template<typename type>	void print(Path<type>*);
template<typename type> Path<type>* DFS(Graph<type>*, type, Path<type>* = nullptr);
template<typename type> Path<type>* BFS(Graph<type>*, type);
template<typename type> Path<type>* BFS_sub_routine(Graph<type>*, type, Path<type>*, uint64_t);


/* classes */
template<typename type>
class Graph {
private:
	std::vector<Graph<type>*> parents;
	std::vector<Graph<type>*> children;
	std::vector<type> checked;
	type data;
public:
	explicit Graph(type data) { this->data = data; }
	explicit Graph(Graph<type>* parent, type data) {
		this->parents.push_back(parent);
		this->data = data;
	}
	//~Graph() { for (auto child : this->children) { delete child; } }

	void add_parent(Graph<type>* parent) {
		this->parents.push_back(parent);
	}
	void add(Graph<type>* new_child) {
		new_child->add_parent(this);
		this->children.push_back(new_child);
	}
	Graph<type>* add(type data) {
		Graph<type>* new_child = new Graph<type>(this, data);
		this->add(new_child); return new_child;
	}

	uint64_t parent_count() const						{ return this->parents.size(); }
	uint64_t child_count() const						{ return this->children.size(); }
	Graph<type>* get_child(uint64_t index) const		{ return this->children[index]; }
	Graph<type>* get_parent(uint64_t index) const		{ return this->parents[index]; }

	uint8_t checked_cleared() const { return this->checked.empty(); }
	void clear_checked() {
		this->checked.clear();
		for (auto child : this->children) { if (!child->checked_cleared()) { child->clear_checked(); } }
	}

	type get_data() const								{ return this->data; }
	uint64_t depth() 									{ uint64_t depth = 0; this->depth(&depth); this->clear_checked(); return depth; }
	void depth(uint64_t* const depth) {
		(*depth)++;
		uint8_t found = 0;
		for (auto child : this->children) {
			for (type c : this->checked) { if (child->data == c) { found = 1; break; } }
			if (found) { continue; }
			this->checked.push_back(child->data);
			child->depth(depth);
		}
	}
	// TODO: node removal


	friend void print<type>(Graph<type>*, const std::string&);
	friend void debug_print<type>(Graph<type>*, const std::string&);
	friend void print<type>(Path<type>*);

	friend Path<type>* DFS<type>(Graph<type>*, type, Path<type>*);
	friend Path<type>* BFS<type>(Graph<type>*, type);
	friend Path<type>* BFS_sub_routine<type>(Graph<type>*, type, Path<type>*, uint64_t);
};


template<typename type>
class Path {  // this class holds a path in a graph
private:
	Graph<type>*			graph = nullptr;
	std::vector<uint64_t>	path;  // array of child indices

	explicit Path(Graph<type>* graph)						{ this->graph = graph; }
	void push(uint64_t step)								{ this->path.push_back(step); }
	void reserve() /* expand the step vector */				{ this->path.push_back(-1); }
	void claim(uint64_t step) /* claim reserved space */	{ this->set(this->path.size() - 1, step); }
	void set(uint64_t index, uint64_t step)					{ this->path[index] = step; }
	void pop()												{ this->path.pop_back(); }

public:
	Path() = delete;  // Path instance may not be created outside the context of a graph search algorithm though you may copy it
	Path(Path& path) {
		this->graph = path.graph;
		for (auto step : path.path) { this->path.push_back(step); }
	}
	// graph is NOT deleted when deleting path

	uint64_t step_count() const					{ return this->path.size(); }
	const uint64_t* steps(uint64_t* size) const { (*size) = this->path.size(); return &this->path[0]; }
	Graph<type>* traverse() const {
		Graph<type>* graph = this->graph;
		for (uint64_t step : this->path) {
			if (!graph) { return (Graph<type>*)nullptr; }
			graph = graph->get_child(step);
		} return graph;
	}


	friend void print<type>(Path<type>*);

	friend Path<type>* DFS<type>(Graph<type>*, type, Path<type>*);
	friend Path<type>* BFS<type>(Graph<type>*, type);
	friend Path<type>* BFS_sub_routine<type>(Graph<type>*, type, Path<type>*, uint64_t);
};


/* friend functions */
template<typename type>
void print(Graph<type>* graph, const std::string& before) {
	std::cout << before << " - (" << graph->data << ")\n";
	const std::string indent = before + " |";
	uint8_t found;
	for (auto child : graph->children) {
		found = 0;
		for (type c : graph->checked) { if (child->data == c) { found = 1; break; } }
		if (found) { continue; } graph->checked.push_back(child->data);
		print(child, indent);
	}
	if (before.empty()) { graph->clear_checked(); std::cout << "\n\n"; }  // root
}

template<typename type>
void debug_print(Graph<type>* graph, const std::string& before) {
	std::cout << before << " - (" << graph->data << ", cc: " << graph->children.size() << ") => [ ";
	for (auto child : graph->children) { std::cout << std::hex << child << " "; }
	std::cout << "]\n";
	const std::string indent = before + " |";
	uint8_t found;
	for (auto child : graph->children) {
		found = 0;
		for (type c : graph->checked) { if (child->data == c) { found = 1; break; } }
		if (found) { continue; } graph->checked.push_back(child->data);
		debug_print(child, indent);
	}
	if (before.empty()) { graph->clear_checked(); std::cout << "\n\n"; }  // root

}

template<typename type>
void print(Path<type>* path) {
	if (!path) { return; }
	const Graph<type>* graph = path->graph;
	std::cout << "(" << graph->data << ")";
	for (uint64_t step : path->path) {
		graph = graph->get_child(step);
		std::cout << " -> (" << graph->data << ")";
	} std::cout << "\n";
}

template<typename type>
Path<type>* DFS(Graph<type>* graph, type data, Path<type>* path) {
	if (!graph) { return nullptr; }
	bool root = !path; if (root) { path = new Path<type>(graph); }
	if (graph->data == data) { return path; }
	path->reserve();  // add temporary entry which will be claimed
	Graph<type>* child;  // loop variable for the graph children
	Path<type>* final_path;  // returned path to data
	uint8_t found;
	for (uint64_t i = 0; i < graph->child_count(); i++) {
		child = graph->get_child(i);
		if (!child) { return nullptr; }  // error
		path->claim(i);
		if (child->data == data) { return path; }
		found = 0;
		for (type c : graph->checked) { if (child->data == c) { found = 1; break; } }
		if (found) { continue; } graph->checked.push_back(child->data);
		final_path = DFS(child, data, path);
		if (final_path) {
			if (root) { graph->clear_checked(); }
			return final_path;
		}
	}
	if (root) { graph->clear_checked(); delete path; }  // failed to construct successful path
	else { path->pop(); }  // pop end of path because it holds a temporary step
	return nullptr;  // not found
}

template<typename type>
Path<type>* BFS(Graph<type>* graph, type data) {
	if (!graph) { return nullptr; }
	uint64_t depth = graph->depth();
	Path<type>* path = new Path<type>(graph);
	Path<type>* final_path;  // returned path to data
	for (uint64_t i = 0; i < depth; i++) {
		final_path = BFS_sub_routine(graph, data, path, i);
		graph->clear_checked();
		if (final_path) { return final_path; }
	}
	delete path;  // failed to construct successful path
	return nullptr;  // not found
}

template<typename type>
Path<type>* BFS_sub_routine(Graph<type>* graph, type data, Path<type>* path, uint64_t depth) {
	if (!graph || !path)		{ return nullptr; }
	if (graph->data == data)	{ return path; }
	if (!depth)					{ return nullptr; }
	depth--;

	Path<type>* final_path;
	Graph<type>* child;
	uint8_t found;

	path->reserve();  // add temporary entry which will be claimed
	for (uint64_t i = 0; i < graph->child_count(); i++) {
		child = graph->get_child(i);
		if (!child) { return nullptr; }  // error
		found = 0;
		for (type c : graph->checked) { if (child->data == c) { found = 1; break; } }
		if (found) { continue; } graph->checked.push_back(child->data);
		path->claim(i);
		final_path = BFS_sub_routine(child, data, path, depth);
		if (final_path) { return final_path; }
	}
	path->pop();
	return nullptr;
}

#endif // PROJECT_GRAPH_H

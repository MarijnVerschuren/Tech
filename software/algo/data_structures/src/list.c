//
// Created by marijn on 3/16/23.
//
#include "list.h"
#include "../inc/list.h"  // this is done so that the ide can find the header file


static void del_node(Node* node, free_func func) {
	if (node->next) { del_node(node->next, func); }
	func(node->data);
	free(node);
}
static Node* get_node(List* list, uint64_t index) {
	if (index >= list->length) { return nullptr; }
	// selecting node and returning its data pointer as readonly
	Node* node = list->head;
	while (index--) { node = node->next; }
	return node;
}

/*!< creation and deletion */
List* new_list(uint64_t data_size) {
	List* list = calloc(1, sizeof(List));
	list->data_size = data_size;
	list->func = &free;
	return list;
}
void set_list_free_func(List* list, free_func func) {
	list->func = func;
}
void del_list(List* list) {
	// delete list and nodes recursively
	if (list->head) { del_node(list->head, list->func); }
	free(list);
}

/*!< indexing and finding */
const void* const list_index(List* list, uint64_t index) {
	// select node and returning its data
	Node* node = get_node(list, index);
	if (!node) { return nullptr; }
	return node->data;
}
List_Error list_get(List* list, uint64_t index, void* ret) {
	// get data by using the index function
	const void* const data = list_index(list, index);
	// copy it to the "ret" buffer
	if (!data) { return index_error; }
	memcpy(ret, data, list->data_size);
	return ok;
}
List_Error list_set(List* list, uint64_t index, void* data) {
	Node* node = get_node(list, index);
	if (!node) { return index_error; }
	memcpy(node->data, data, list->data_size);
	return ok;
}
uint64_t list_find(List* list, void* data, cmp_func cmp) {
	Node* node = list->head;
	uint64_t i = 0;
	for (; i < list->length && !cmp(node->data, data); i++) {
		node = node->next;
	} return i;
}
uint64_t list_rfind(List* list, void* data, cmp_func cmp) {
	Node* node = list->head;
	uint64_t i = list->length;
	for (; i && !cmp(node->data, data); i--) {
		node = node->next;
	} return i;
}

/*!< functions */
List_Error list_append(List* list, void* data) {
	// creating node
	Node* node = calloc(1, sizeof(Node));
	node->data = malloc(list->data_size);
	memcpy(node->data, data, list->data_size);
	// linking node and updating length
	if (!list->tail) {
		list->head = node;
		list->tail = node;
		list->length = 1;
		return;
	}
	list->tail->next = node;
	node->prev = list->tail;
	list->tail = node;
	list->length++;
	return ok;
}
List_Error list_insert(List* list, void* data, uint64_t index) {
	// select node
	Node* node = get_node(list, index);
	if (!node) { return index_error; }
	// creating node, linking it and updating length
	Node* prev = node->prev;
	Node* new = malloc(sizeof(Node));
	new->next = node;
	new->prev = prev;
	node->prev = new;
	if (prev)	{ prev->next = new; }
	else		{list->head = new; }
	new->data = malloc(list->data_size);
	memcpy(new->data, data, list->data_size);
	list->length++;
	return ok;
}
List_Error list_pop(List* list) {
	if (!list->length) { return list_empty; }
	// free memory
	list->func(list->tail->data);
	free(list->tail);
	// fix tail and update length
	Node* prev = list->tail->prev;
	prev->next = nullptr;
	list->tail = prev;
	list->length--;
	return ok;
}
List_Error list_remove(List* list, uint64_t index) {
	// special cases
	if (index >= list->length)			{ return index_error; }
	else if (index == list->length - 1)	{ return list_pop(list); }
	// select node to remove
	Node* node = get_node(list, index);
	// fix both neighboring nodes
	Node* prev = node->prev;
	Node* next = node->next;
	prev->next = next;
	next->prev = prev;
	// free memory and updating length
	list->func(node->data);
	free(node);
	list->length--;
	return ok;
}

/*!< splitting and merging */
List* split_list(List* list, uint64_t index) {
	// select node to split on
	Node* node = get_node(list, index);
	if (!node) { return nullptr; }
	// update lengths
	List* ret = new_list(list->data_size);
	set_list_free_func(ret, list->func);
	ret->length = list->length - index;
	list->length = index;
	// fix ends of list
	ret->head = node;
	ret->tail = list->tail;
	list->tail = node->prev;
	list->tail->next = nullptr;
	ret->head->prev = nullptr;
	return ret;
}
List_Error extend_list(List* dst, List* src) {
	Node* end = dst->tail;
	dst->tail = src->tail;
	src->head->prev = end;
	end->next = src->head;
	dst->length += src->length;
	src->head = nullptr;
	del_list(src);
	return ok;
}
List_Error merge_list(List* dst, List* src, uint64_t index) {
	Node* next = get_node(dst, index);
	if (!next) { return index_error; }
	Node* prev = next->prev;
	prev->next = src->head;
	src->head->prev = prev;
	next->prev = src->tail;
	src->tail->next = next;
	dst->length += src->length;
	src->head = nullptr;
	del_list(src);
	return ok;
}
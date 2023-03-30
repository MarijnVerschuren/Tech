//
// Created by marijn on 3/16/23.
//

#ifndef DATA_STRUCTURES_LIST_H
#define DATA_STRUCTURES_LIST_H

#include "main.h"


/*!< types */
typedef void (*free_func)(void*);
typedef uint8_t (*cmp_func)(void*, void*);

typedef struct {
	void* data;
	void* next;
	void* prev;
} Node;

typedef struct {
	Node* head;
	Node* tail;
	uint64_t length;
	uint64_t data_size;
	free_func func;  // set to free by default
} List;
// List -> head .... tail

/*!< creation configuration and deletion */
List* new_list(uint64_t data_size);
void set_list_free_func(List* list, free_func func);
void del_list(List* list);

/*!< indexing, setting and finding */
const void* const list_index(List* list, uint64_t index);	// result is readonly
Status list_get(List* list, uint64_t index, void* ret);	// result is read-write
Status list_set(List* list, uint64_t index, void* data);
uint64_t list_find(List* list, void* data, cmp_func cmp);
uint64_t list_rfind(List* list, void* data, cmp_func cmp);

/*!< addition and removal */
Status list_append(List* list, void* data);
Status list_insert(List* list, void* data, uint64_t index);
Status list_pop(List* list);
Status list_remove(List* list, uint64_t index);

/*!< splitting and merging */
List* split_list(List* list, uint64_t index);
Status extend_list(List* dst, List* src);					// deletes src
Status merge_list(List* dst, List* src, uint64_t index);	// deletes src


#endif //DATA_STRUCTURES_LIST_H

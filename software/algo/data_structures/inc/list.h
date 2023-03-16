//
// Created by marijn on 3/16/23.
//

#ifndef DATA_STRUCTURES_LIST_H
#define DATA_STRUCTURES_LIST_H

#include "main.h"


/*!< types */
typedef void (*free_func)(void*);

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

/*!< errors
 * \n 0x00 - 0x0f: soft error
 * \n 0x10 - 0xf0: hard fault */
typedef enum {
	ok = 0x00,
	list_empty = 0x01,
	index_error = 0x10,
} List_Error;

/*!< creation configuration and deletion */
List* new_list(uint64_t data_size);
void set_list_free_func(List* list, free_func func);
void del_list(List* list);

/*!< indexing, setting and finding */
const void* const list_index(List* list, uint64_t index);	// result is readonly
List_Error list_get(List* list, uint64_t index, void* ret);	// result is read-write
// TODO: setters
// TODO: find/rfind

/*!< addition and removal */
void list_append(List* list, void* data);
List_Error list_insert(List* list, void* data, uint64_t index);
List_Error list_pop(List* list);
List_Error list_remove(List* list, uint64_t index);

/*!< splitting and merging */
List* split_list(List* list, uint64_t index);
// TODO: merge

#endif //DATA_STRUCTURES_LIST_H

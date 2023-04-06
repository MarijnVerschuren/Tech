
#include "mystack.h"
#include "logging.h"
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
/* The stack is an abstract data type.
* this means that the internal structures are
* never exposed to the users of the library.
*/

/* Note: the stacks have no knowledge of what types
* they are storing. This is not a concern of the stack
*/

StackMeta_t *mystack_create(size_t objsize) {
	if (!objsize) { return NULL; }
	StackMeta_t* stack = calloc(1, sizeof(StackMeta_t));
	if (!stack) { return NULL; }
	stack->objsize = objsize;
	return stack;
}

int mystack_push(StackMeta_t *stack, void* obj) {
	if (!stack || !obj) { return -1; }
	StackObject_t* next = stack->stack;
	StackObject_t* new = malloc(sizeof(StackObject_t));
	if (!new) { return -1; }
	new->next = next;
	new->obj = malloc(stack->objsize);
	memcpy(new->obj, obj, stack->objsize);
	stack->stack = new;
	stack->numelem++;
	return 0;
}

int mystack_pop(StackMeta_t *stack, void* obj) {
	if (!stack || !obj) { return -1; }
	StackObject_t* pop = stack->stack;
	StackObject_t* next = pop->next;
	memcpy(obj, pop->obj, stack->objsize);
	free(pop->obj); free(pop);
	stack->stack = next;
	stack->numelem--;
	return 0;
}


static void destroy_chain(StackObject_t* obj) {
	if (!obj) { return; }
	if (obj->next) {
		destroy_chain(obj->next);
		free(obj->next); obj->next = NULL;
	}
	free(obj->obj);
}

void mystack_destroy(StackMeta_t *stack) {
	if (!stack) { return; }
	destroy_chain(stack->stack);
	free(stack->stack);  // first element is not deleted by destroy_chain
	free(stack);
}

int mystack_nofelem(StackMeta_t *stack) {
	if (!stack) { return -1; }
	return stack->numelem;
}

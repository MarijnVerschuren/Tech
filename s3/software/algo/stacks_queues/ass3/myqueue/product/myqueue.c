#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <unistd.h>

#include "mystack.h"
#include "myqueue.h"


QueueMeta_t *myqueue_create(int item_size) {
	if (item_size <= 0) { return NULL; }
	QueueMeta_t* handle = malloc(sizeof(QueueMeta_t));
	if (!handle) { return NULL; }
	handle->stack_in = NULL;
	handle->stack_out = NULL;
	handle->item_size = item_size;
	return handle;
}

void myqueue_delete(QueueMeta_t *queue) {
	if (!queue) { return; }
	QueueObject_t *current, *next = queue->stack_in;
	if (!next) { free(queue); return; }
	do {
		current = next;
		next = current->next;
		free(current->obj);
		free(current);
	} while (next);
	free(queue);
}

int myqueue_enqueue(QueueMeta_t *queue, void *obj) {
	if (!queue || !obj) { return -1; }
	QueueObject_t* q_obj = malloc(sizeof(QueueObject_t));
	if (!q_obj) { return -1; }
	q_obj->prev = NULL;
	q_obj->obj = malloc(queue->item_size);
	if (!q_obj->obj) { return -1; }
	if (!queue->stack_out) { queue->stack_out = q_obj; }
	if (queue->stack_in) { queue->stack_in->prev = q_obj; }
	q_obj->next = queue->stack_in;
	queue->stack_in = q_obj;
	memcpy(q_obj->obj, obj, queue->item_size);
	return 0;
}

int myqueue_dequeue(QueueMeta_t *queue, void *obj) {
	if (!queue) { return -1; }
	if (!queue->stack_out) { return -1; }
	if (obj) { memcpy(obj, queue->stack_out->obj, queue->item_size); }
	QueueObject_t* out = queue->stack_out;
	if (queue->stack_in == queue->stack_out) { queue->stack_in = NULL; }
	queue->stack_out = out->prev;
	queue->stack_out->next = NULL;
	free(out->obj);
	free(out);
	return 0;
}

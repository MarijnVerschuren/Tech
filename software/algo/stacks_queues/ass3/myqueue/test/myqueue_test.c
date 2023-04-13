#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include "mystack.h"
#include "myqueue.h"
#include "unity.h"
#include "testrunner.h"

// I rather dislike keeping line numbers updated, so I made my own macro to ditch the line number
#define MY_RUN_TEST(func) RUN_TEST(func, 0)

QueueMeta_t* queue;
uint64_t obj = 0x676ab83c7a3be4df;


void setUp(void) {
	queue = myqueue_create(sizeof(uint64_t));
}

void tearDown(void) {
	myqueue_delete(queue);
}

void test_queue_create_delete(void) {
	QueueMeta_t* test_queue = myqueue_create(sizeof(uint8_t));
	TEST_ASSERT_NOT_EQUAL(NULL, test_queue)
	TEST_ASSERT_NULL((void*)test_queue->stack_in)
	TEST_ASSERT_NULL((void*)test_queue->stack_out)
	TEST_ASSERT_EQUAL(sizeof(uint8_t), test_queue->item_size);
	myqueue_delete(test_queue);
}

void test_enqueue_dequeue(void) {
	TEST_ASSERT_EQUAL(0, myqueue_enqueue(queue, &obj));
	TEST_ASSERT_EQUAL(-1, myqueue_enqueue(queue, NULL));
	TEST_ASSERT_EQUAL(-1, myqueue_enqueue(NULL, NULL));

	TEST_ASSERT_EQUAL(obj, *((uint64_t*)queue->stack_in->obj));
	TEST_ASSERT_NULL(queue->stack_in->prev)
	TEST_ASSERT_NULL(queue->stack_in->next)
	TEST_ASSERT_EQUAL(queue->stack_in, queue->stack_out);
	myqueue_enqueue(queue, &obj);
	TEST_ASSERT_NOT_EQUAL(queue->stack_in, queue->stack_out)
	TEST_ASSERT_EQUAL(queue->stack_in, queue->stack_out->prev);
	TEST_ASSERT_EQUAL(queue->stack_out, queue->stack_in->next);

	myqueue_enqueue(queue, &obj);  // add more elements to test data deletion
	myqueue_enqueue(queue, &obj);
	myqueue_enqueue(queue, &obj);
}


int main () {
	UnityBegin();
	MY_RUN_TEST(test_queue_create_delete);
	MY_RUN_TEST(test_enqueue_dequeue);
	return UnityEnd();
}

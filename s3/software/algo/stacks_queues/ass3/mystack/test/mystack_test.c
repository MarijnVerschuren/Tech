#include <string.h>
#include <stdio.h>
#include <stdint.h>

#include "mystack.h"
#include "unity.h"
#include "testrunner.h"

// I rather dislike keeping line numbers updated, so I made my own macro to ditch the line number
#define MY_RUN_TEST(func) RUN_TEST(func, 0)

StackMeta_t* stack;
uint64_t obj = 29834923498234;  // test data


void setUp(void) { stack = mystack_create(sizeof(uint64_t)); }
void tearDown(void) { mystack_destroy(stack); stack = NULL; }

void push_test(void) {
	TEST_ASSERT_EQUAL(0, mystack_push(stack, &obj));
	TEST_ASSERT_EQUAL(-1, mystack_push(stack, NULL));
	TEST_ASSERT_EQUAL(-1, mystack_push(NULL, NULL));

	TEST_ASSERT_EQUAL(obj, *(uint64_t*)stack->stack->obj);
	TEST_ASSERT_EQUAL(1, stack->numelem);

	void* next = stack->stack;
	TEST_ASSERT_EQUAL(0, mystack_push(stack, &obj));
	TEST_ASSERT_EQUAL((uint64_t)next, (uint64_t)stack->stack->next);
	TEST_ASSERT_EQUAL(2, stack->numelem);
}

void pop_test(void) {
	uint64_t dat;
	mystack_push(stack, &obj);  // adding two entries to be popped
	mystack_push(stack, &obj);
	TEST_ASSERT_EQUAL(0, mystack_pop(stack, &dat));
	TEST_ASSERT_EQUAL(obj, dat);
	TEST_ASSERT_EQUAL(0, mystack_pop(stack, NULL));
	TEST_ASSERT_EQUAL(-1, mystack_pop(NULL, NULL));
	TEST_ASSERT_EQUAL(0, stack->numelem);
}

void nofelem_test(void) {
	TEST_ASSERT_EQUAL(sizeof(uint64_t), stack->objsize);
	TEST_ASSERT_EQUAL(0, stack->numelem);
	TEST_ASSERT_EQUAL(0, mystack_nofelem(stack));
	TEST_ASSERT_EQUAL(-1, mystack_nofelem(NULL));
}

int main (int argc, char * argv[]) {
	UnityBegin();
	MY_RUN_TEST(nofelem_test);
	MY_RUN_TEST(push_test);
	MY_RUN_TEST(pop_test);
	return UnityEnd();
}

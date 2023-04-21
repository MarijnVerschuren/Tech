#include <string.h>

#include "linkedlist.h"
#include "unity.h"

#define MY_RUN_TEST(func) RUN_TEST(func, 0)


void setUp(void)
{
    // This is run before EACH test
}

void tearDown(void)
{
  // This is run after EACH test
}

void test_add_first(void)
{
  int ret;
  ITEM *list = NULL;
  ret = add_first(&list, 1);
  TEST_ASSERT_EQUAL(0, ret);
  clean(&list);
}

int main (int argc, char * argv[])
{
    UnityBegin();

    /* Put your UTs here */
    MY_RUN_TEST(test_add_first);

    return UnityEnd();
}

#include <string.h>
#include <stdio.h>

#include "mystack.h"
#include "unity.h"

// I rather dislike keeping line numbers updated, so I made my own macro to ditch the line number
#define MY_RUN_TEST(func) RUN_TEST(func, 0)

void setUp(void)
{
}

void tearDown(void)
{
    // This is run after EACH test
}

void test_setting_time_hours(void)
{
}

int main (int argc, char * argv[])
{
    UnityBegin();

    MY_RUN_TEST(test_setting_time_hours);

    return UnityEnd();
}

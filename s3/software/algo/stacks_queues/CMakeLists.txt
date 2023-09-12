cmake_minimum_required(VERSION 3.24)
project(stacks_queues)

set(CMAKE_CXX_STANDARD 14)

include_directories(ass3/myqueue/product)
include_directories(ass3/myqueue/Unity)
include_directories(ass3/mystack/product)
include_directories(ass3/mystack/Unity)

add_executable(stacks_queues
        ass3/3/ass3.c
        ass3/myqueue/product/myqueue.c
        ass3/myqueue/product/myqueue.h
        ass3/myqueue/test/myqueue_test.c
        ass3/myqueue/Unity/testrunner.c
        ass3/myqueue/Unity/testrunner.h
        ass3/myqueue/Unity/unity.c
        ass3/myqueue/Unity/unity.h
        ass3/myqueue/Unity/unity_internals.h
        ass3/mystack/product/logging.h
        ass3/mystack/product/main.c
        ass3/mystack/product/mystack.c
        ass3/mystack/product/mystack.h
        ass3/mystack/test/mystack_test.c
        ass3/mystack/Unity/testrunner.c
        ass3/mystack/Unity/testrunner.h
        ass3/mystack/Unity/unity.c
        ass3/mystack/Unity/unity.h
        ass3/mystack/Unity/unity_internals.h
        obsolete/quick_sketch_for_stack_assignment.jpg
        src/beschrijving.md
        src/links.md)

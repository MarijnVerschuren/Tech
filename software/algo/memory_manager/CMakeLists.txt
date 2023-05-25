cmake_minimum_required(VERSION 3.25)
project(memory_manager)

set(CMAKE_CXX_STANDARD 14)

include_directories(ass5/product)

link_libraries(
        -lgtest -lgmock_main -lpthread -lgmock
)

add_executable(memory_manager
        ass5/product/MemoryManager.cpp
        ass5/product/MemoryManager.h
        ass5/product/MList.cpp
        ass5/product/MList.h
        ass5/product/testUi.cpp
        ass5/product/testUi.h
        ass5/test/mytests.cpp
        ass5/main.cpp)

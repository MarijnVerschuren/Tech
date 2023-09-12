cmake_minimum_required(VERSION 3.25)
project(lib_c++)

set(CMAKE_CXX_STANDARD 14)

include_directories(ass4/LLExample/cpp/product)
include_directories(ass4/LLExample/cpp/test)

link_libraries(
        -lgtest -lgmock_main -lpthread -lgmock
)

add_executable(lib_c__
        ass4/LLExample/cpp/product/linkedList.cpp
        ass4/LLExample/cpp/product/linkedList.h
        ass4/LLExample/cpp/test/Test.cpp
)

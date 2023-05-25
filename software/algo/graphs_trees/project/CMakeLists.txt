cmake_minimum_required(VERSION 3.25)
project(project)

set(CMAKE_CXX_STANDARD 23)

include_directories(./inc)
add_executable(project src/main.cpp)

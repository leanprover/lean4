cmake_minimum_required (VERSION 2.8.7)
project (LEAN CXX)
set (LEAN_VERSION_MAJOR 0)
set (LEAN_VERSION_MINOR 1)
set (CMAKE_CXX_COMPILER "g++-4.8")
set (CMAKE_CXX_FLAGS_DEBUG "-DLEAN_DEBUG -DLEAN_TRACE -g")
set (CMAKE_CXX_FLAGS_RELEASE "-O3")
set (CMAKE_COLOR_MAKEFILE ON)
add_definitions(-std=c++11 -Wall)

add_subdirectory(util)
add_subdirectory(shell)


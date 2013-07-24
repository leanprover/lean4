cmake_minimum_required(VERSION 2.8.7)
project(LEAN CXX)
set(LEAN_VERSION_MAJOR 0)
set(LEAN_VERSION_MINOR 1)

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "-Wall -std=c++11")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DLEAN_DEBUG -DLEAN_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

# Compiler-specific C++11 activation.
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
    execute_process(
        COMMAND ${CMAKE_CXX_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)
    if (NOT (GCC_VERSION VERSION_GREATER 4.8 OR GCC_VERSION VERSION_EQUAL 4.8))
        message(FATAL_ERROR "${PROJECT_NAME} requires g++ 4.8 or greater.")
    endif ()
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  # Do nothing
else ()
    message(FATAL_ERROR "Your C++ compiler does not support C++11.")
endif ()

# GMP
include(cmake/FindGMP.cmake)
set(EXTRA_LIBS ${EXTRA_LIBS} ${GMP_LIBRARIES})

# tcmalloc
option(tcmalloc "tcmalloc" ON)
if("${tcmalloc}" MATCHES "ON")
  include(cmake/FindTcmalloc.cmake)
  if(${TCMALLOC_FOUND})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARIES})
  endif()
else()
  message("-- Using standard malloc.")
endif()

include_directories(${LEAN_SOURCE_DIR}/util)
include_directories(${LEAN_SOURCE_DIR}/util/numerics)
include_directories(${LEAN_SOURCE_DIR}/util/sexpr)
include_directories(${LEAN_SOURCE_DIR}/interval)
include_directories(${LEAN_SOURCE_DIR}/kernel)

add_subdirectory(util)
set(EXTRA_LIBS ${EXTRA_LIBS} util)
add_subdirectory(util/numerics)
set(EXTRA_LIBS ${EXTRA_LIBS} numerics)
add_subdirectory(util/sexpr)
set(EXTRA_LIBS ${EXTRA_LIBS} sexpr)
add_subdirectory(interval)
set(EXTRA_LIBS ${EXTRA_LIBS} interval)
add_subdirectory(kernel)
set(EXTRA_LIBS ${EXTRA_LIBS} kernel)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread")
add_subdirectory(shell)
add_subdirectory(tests/util)
add_subdirectory(tests/util/numerics)
add_subdirectory(tests/util/sexpr)
add_subdirectory(tests/interval)
add_subdirectory(tests/kernel)

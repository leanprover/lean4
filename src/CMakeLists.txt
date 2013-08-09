cmake_minimum_required(VERSION 2.8.7)
project(LEAN CXX)
set(LEAN_VERSION_MAJOR 0)
set(LEAN_VERSION_MINOR 1)

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

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
find_package(GMP 5.0.5)
set(EXTRA_LIBS ${EXTRA_LIBS} ${GMP_LIBRARIES})

# MPFR
find_package(MPFR 3.1.0)
set(EXTRA_LIBS ${EXTRA_LIBS} ${MPFR_LIBRARIES})

# Flex and Bison
find_package(FLEX REQUIRED)

# tcmalloc
option(tcmalloc "tcmalloc" ON)
if("${tcmalloc}" MATCHES "ON")
  if(${TCMALLOC_FOUND})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARIES})
  endif()
else()
  message("-- Using standard malloc.")
endif()

include_directories(${LEAN_SOURCE_DIR}/util)
include_directories(${LEAN_SOURCE_DIR}/util/numerics)
include_directories(${LEAN_SOURCE_DIR}/interval)
include_directories(${LEAN_SOURCE_DIR}/kernel)
include_directories(${LEAN_SOURCE_DIR}/kernel/arith)
include_directories(${LEAN_SOURCE_DIR}/parsers)
include_directories(${LEAN_SOURCE_DIR}/frontend)

add_subdirectory(util)
set(EXTRA_LIBS ${EXTRA_LIBS} util)
add_subdirectory(util/numerics)
set(EXTRA_LIBS ${EXTRA_LIBS} numerics)
add_subdirectory(interval)
set(EXTRA_LIBS ${EXTRA_LIBS} interval)
add_subdirectory(kernel)
set(EXTRA_LIBS ${EXTRA_LIBS} kernel)
add_subdirectory(kernel/arith)
set(EXTRA_LIBS ${EXTRA_LIBS} kernel_arith)
add_subdirectory(frontend)
set(EXTRA_LIBS ${EXTRA_LIBS} frontend)
add_subdirectory(parsers)
set(EXTRA_LIBS ${EXTRA_LIBS} parser_common)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread")
add_subdirectory(shell)
add_subdirectory(tests/util)
add_subdirectory(tests/util/numerics)
add_subdirectory(tests/interval)
add_subdirectory(tests/kernel)
add_subdirectory(tests/frontend)

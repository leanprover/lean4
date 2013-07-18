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

if (GMP_INCLUDE_DIR AND GMP_LIBRARIES)
   # Already in cache, be silent
   set(GMP_FIND_QUIETLY TRUE)
endif (GMP_INCLUDE_DIR AND GMP_LIBRARIES)

find_path(GMP_INCLUDE_DIR NAMES gmp.h )
find_library(GMP_LIBRARIES NAMES gmp libgmp REQUIRED)
message(STATUS "GMP: " ${GMP_LIBRARIES})

find_library(TCMALLOC_LIBRARY tcmalloc)
if (${TCMALLOC_LIBRARY} MATCHES "TCMALLOC_LIBRARY-NOTFOUND")
  message("*** WARNING: failed to find tcmalloc")
  message("*** The (optional) tcmalloc library is available at: https://code.google.com/p/gperftools")
else()
  message("Found tcmalloc")
  set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARY})
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP DEFAULT_MSG GMP_INCLUDE_DIR GMP_LIBRARIES)
mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARIES)

include_directories(${LEAN_SOURCE_DIR}/util) 
include_directories(${LEAN_SOURCE_DIR}/numerics) 
add_subdirectory(util)
add_subdirectory(numerics)
set(EXTRA_LIBS ${EXTRA_LIBS} util numerics ${GMP_LIBRARIES})
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread")
add_subdirectory(shell)
add_subdirectory(tests/numerics)


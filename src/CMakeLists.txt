cmake_minimum_required(VERSION 2.8.7)
project(LEAN CXX)
set(LEAN_VERSION_MAJOR 0)
set(LEAN_VERSION_MINOR 1)

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

set(LEAN_EXTRA_LINKER_FLAGS "")

# Cygwin: Windows does not support ulimit -s unlimited. So, we reserve a lot of stack space: 100Mb
if(${CYGWIN})
  message(STATUS "CYGWIN detected")
  set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -Wl,--stack,104857600")
endif()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "-Wall -std=c++11")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DLEAN_DEBUG -DLEAN_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")
set(CMAKE_CXX_FLAGS_TESTCOV   "${CMAKE_CXX_FLAGS_DEBUG} -fprofile-arcs -ftest-coverage")

# Compiler-specific C++11 activation.
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
    execute_process(
        COMMAND ${CMAKE_CXX_COMPILER} -dumpversion OUTPUT_VARIABLE GCC_VERSION)
    if (NOT (GCC_VERSION VERSION_GREATER 4.8 OR GCC_VERSION VERSION_EQUAL 4.8))
        message(FATAL_ERROR "${PROJECT_NAME} requires g++ 4.8 or greater.")
    endif ()
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # In OSX, clang requires "-stdlib=libc++" to support C++11
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
    set(LEAN_EXTRA_LINKER_FLAGS "-stdlib=libc++")
  endif ()
else ()
    message(FATAL_ERROR "Your C++ compiler does not support C++11.")
endif ()

# GMP
find_package(GMP 5.0.5)
set(EXTRA_LIBS ${EXTRA_LIBS} ${GMP_LIBRARIES})

# MPFR
find_package(MPFR 3.1.0)
set(EXTRA_LIBS ${EXTRA_LIBS} ${MPFR_LIBRARIES})

# tcmalloc
option(TCMALLOC "TCMALLOC" ON)
if("${TCMALLOC}" MATCHES "ON")
  if(${TCMALLOC_FOUND})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARIES})
  endif()
  message(STATUS "Using tcmalloc.")
else()
  message(STATUS "Using standard malloc.")
endif()

# Readline
option(READLINE "READLINE" OFF)
if("${READLINE}" MATCHES "ON")
  find_package(Readline)
  set(EXTRA_LIBS ${EXTRA_LIBS} ${READLINE_LIBRARY})
  message(STATUS "Using GNU readline")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DLEAN_USE_READLINE")
endif()

include_directories(${LEAN_SOURCE_DIR}/util)
include_directories(${LEAN_SOURCE_DIR}/util/numerics)
include_directories(${LEAN_SOURCE_DIR}/util/sexpr)
include_directories(${LEAN_SOURCE_DIR}/interval)
include_directories(${LEAN_SOURCE_DIR}/kernel)
include_directories(${LEAN_SOURCE_DIR}/kernel/arith)
include_directories(${LEAN_SOURCE_DIR}/exprlib)
include_directories(${LEAN_SOURCE_DIR}/parsers)
include_directories(${LEAN_SOURCE_DIR}/frontends/lean)

add_subdirectory(util)
set(LEAN_LIBS ${LEAN_LIBS} util)
add_subdirectory(util/numerics)
set(LEAN_LIBS ${LEAN_LIBS} numerics)
add_subdirectory(util/sexpr)
set(LEAN_LIBS ${LEAN_LIBS} sexpr)
add_subdirectory(interval)
set(LEAN_LIBS ${LEAN_LIBS} interval)
add_subdirectory(kernel)
set(LEAN_LIBS ${LEAN_LIBS} kernel)
add_subdirectory(kernel/arith)
set(LEAN_LIBS ${LEAN_LIBS} kernel_arith)
add_subdirectory(exprlib)
set(LEAN_LIBS ${LEAN_LIBS} exprlib)
add_subdirectory(frontends/lean)
set(LEAN_LIBS ${LEAN_LIBS} lean_frontend)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread ${LEAN_EXTRA_LINKER_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")
set(EXTRA_LIBS ${LEAN_LIBS} ${EXTRA_LIBS})
add_subdirectory(shell)
add_subdirectory(tests/util)
add_subdirectory(tests/util/numerics)
add_subdirectory(tests/interval)
add_subdirectory(tests/kernel)
add_subdirectory(tests/frontends/lean)

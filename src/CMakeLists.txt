cmake_minimum_required(VERSION 2.8.7)
project(LEAN CXX)
set(LEAN_VERSION_MAJOR 0)
set(LEAN_VERSION_MINOR 1)

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(TRACK_MEMORY_USAGE "TRACK_MEMORY_USAGE" ON)
option(MULTI_THREAD       "MULTI_THREAD"       ON)
option(BOOST              "BOOST"              OFF)
option(STATIC             "STATIC"             OFF)
option(SPLIT_STACK        "SPLIT_STACK"        OFF)

# Added for CTest
INCLUDE(CTest)
CONFIGURE_FILE(${LEAN_SOURCE_DIR}/CTestCustom.cmake.in
  ${LEAN_BINARY_DIR}/CTestCustom.cmake @ONLY)

set(LEAN_EXTRA_LINKER_FLAGS "")
set(LEAN_EXTRA_CXX_FLAGS "")

# Windows does not support ulimit -s unlimited. So, we reserve a lot of stack space: 100Mb
if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  message(STATUS "Windows detected")
  set(LEAN_WIN_STACK_SIZE "104857600")
  set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -Wl,--stack,${LEAN_WIN_STACK_SIZE}")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_DEFAULT_PP_UNICODE=false")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_WINDOWS -D LEAN_WIN_STACK_SIZE=${LEAN_WIN_STACK_SIZE}")
endif()

if("${MULTI_THREAD}" MATCHES "OFF")
  message(STATUS "Disabled multi-thread support, it will not be safe to run multiple threads in parallel")
else()
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_MULTI_THREAD")
endif()

if("${STATIC}" MATCHES "ON")
  set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -static")
  message(STATUS "Creating a static executable")
endif()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${LEAN_EXTRA_CXX_FLAGS}")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DLEAN_DEBUG -DLEAN_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")

# SPLIT_STACK
if ("${SPLIT_STACK}" MATCHES "ON")
  if ((${CMAKE_SYSTEM_NAME} MATCHES "Linux") AND ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
     set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsplit-stack -D LEAN_USE_SPLIT_STACK")
     message(STATUS "Using split-stacks")
  else()
     message(FATAL_ERROR "Split-stacks are only supported on Linux with g++")
  endif()
endif()

# Test coverage
if("${TESTCOV}" MATCHES "ON")
  include(CodeCoverage)
  message(STATUS "Enable test-coverage")
  set(CMAKE_CXX_FLAGS_DEBUG        "${CMAKE_CXX_FLAGS_DEBUG} -O0 -fprofile-arcs -ftest-coverage --coverage")
  setup_target_for_coverage(cov ${LEAN_SOURCE_DIR}/../script/run_tests.sh coverage)
endif()

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

# BOOST
if (("${BOOST}" MATCHES "ON") AND ("${MULTI_THREAD}" MATCHES "ON"))
  find_package(Boost 1.54 COMPONENTS system thread atomic chrono REQUIRED)
  message(STATUS "Boost library will be used to implement multi-threading support")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D LEAN_USE_BOOST")
  set(EXTRA_LIBS ${EXTRA_LIBS} -lboost_system -lboost_chrono -lboost_atomic -lboost_thread)
endif()

# MPFR
find_package(MPFR 3.1.0)
include_directories(${MPFR_INCLUDES})
set(EXTRA_LIBS ${EXTRA_LIBS} ${MPFR_LIBRARIES})

# GMP
find_package(GMP 5.0.5)
include_directories(${GMP_INCLUDE_DIR})
set(EXTRA_LIBS ${EXTRA_LIBS} ${GMP_LIBRARIES})

# TRACK_MEMORY_USAGE
if("${TRACK_MEMORY_USAGE}" MATCHES "ON")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D LEAN_TRACK_MEMORY")
endif()

# tcmalloc
option(TCMALLOC "TCMALLOC" ON)
if("${TCMALLOC}" MATCHES "ON")
  find_package(Tcmalloc)
  if(${TCMALLOC_FOUND})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARIES})
    message(STATUS "Using tcmalloc.")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D HAS_TCMALLOC")
  else()
    message(WARNING "FAILED to find tcmalloc, using standard malloc.")
  endif()
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

# Check malloc_usable_size
if(NOT "${TCMALLOC_FOUND}" AND "${TRACK_MEMORY_USAGE}" MATCHES "ON")
  find_package(MallocUsableSize)
  if("${MUS_FOUND}" MATCHES "TRUE")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${MALLOC_DIR} -D HAS_MALLOC_USABLE_SIZE")
  else()
    find_package(MallocSize)
    if("${MALLOCSIZE_FOUND}" MATCHES "TRUE")
      set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${MALLOC_DIR} -D HAS_MALLOCSIZE")
    else()
      find_package(MSize)
      if("${MSIZE_FOUND}" MATCHES "TRUE")
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${MALLOC_DIR} -D HAS_MSIZE")
      endif()
    endif()
  endif()
endif()

find_package(Lua REQUIRED)
set(EXTRA_LIBS ${EXTRA_LIBS} ${LUA_LIBRARIES})
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  # Lua static library for linux depends on dl.so
  set(EXTRA_LIBS ${EXTRA_LIBS} -ldl)
endif()
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${LUA_INCLUDE_DIR}")
if ("${HAS_LUA_NEWSTATE}$" MATCHES "TRUE")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D LEAN_USE_LUA_NEWSTATE")
endif()

include_directories(${LEAN_SOURCE_DIR})

add_custom_command(
  OUTPUT ${LEAN_BINARY_DIR}/githash.h
  COMMAND ${LEAN_SOURCE_DIR}/cmake/mk_githash_dot_h.sh ${LEAN_BINARY_DIR}
  DEPENDS ${LEAN_SOURCE_DIR}/../.git/HEAD ${LEAN_SOURCE_DIR}/../.git/index
)
add_custom_target(githash
  DEPENDS ${LEAN_BINARY_DIR}/githash.h ${LEAN_SOURCE_DIR}/../.git/HEAD ${LEAN_SOURCE_DIR}/../.git/index
)

add_subdirectory(util)
set(LEAN_LIBS ${LEAN_LIBS} util)
add_subdirectory(util/numerics)
set(LEAN_LIBS ${LEAN_LIBS} numerics)
add_subdirectory(util/sexpr)
set(LEAN_LIBS ${LEAN_LIBS} sexpr)
add_subdirectory(util/interval)
set(LEAN_LIBS ${LEAN_LIBS} interval)
add_subdirectory(kernel)
set(LEAN_LIBS ${LEAN_LIBS} kernel)
add_subdirectory(library)
set(LEAN_LIBS ${LEAN_LIBS} library)
add_subdirectory(library/arith)
set(LEAN_LIBS ${LEAN_LIBS} arithlib)
add_subdirectory(library/cast)
set(LEAN_LIBS ${LEAN_LIBS} castlib)
add_subdirectory(library/all)
set(LEAN_LIBS ${LEAN_LIBS} alllib)
add_subdirectory(library/rewriter)
set(LEAN_LIBS ${LEAN_LIBS} rewriter)
add_subdirectory(library/elaborator)
set(LEAN_LIBS ${LEAN_LIBS} elaborator)
add_subdirectory(library/tactic)
set(LEAN_LIBS ${LEAN_LIBS} tactic)
add_subdirectory(frontends/lean)
set(LEAN_LIBS ${LEAN_LIBS} lean_frontend)
add_subdirectory(frontends/lua)
set(LEAN_LIBS ${LEAN_LIBS} leanlua)
if("${MULTI_THREAD}" MATCHES "ON")
   set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread ${LEAN_EXTRA_LINKER_FLAGS}")
else()
   set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LEAN_EXTRA_LINKER_FLAGS}")
endif()
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")
set(EXTRA_LIBS ${LEAN_LIBS} ${EXTRA_LIBS})
add_subdirectory(shell)
add_subdirectory(tests/util)
add_subdirectory(tests/util/numerics)
add_subdirectory(tests/util/interval)
add_subdirectory(tests/kernel)
add_subdirectory(tests/library)
add_subdirectory(tests/library/rewriter)
add_subdirectory(tests/library/tactic)
add_subdirectory(tests/library/elaborator)
add_subdirectory(tests/frontends/lean)

# Include style check
include(StyleCheck)
file(GLOB_RECURSE LEAN_SOURCES
         ${LEAN_SOURCE_DIR}
         ${LEAN_SOURCE_DIR}/[A-Za-z]*.cpp
         ${LEAN_SOURCE_DIR}/[A-Za-z]*.h)
add_style_check_target(style "${LEAN_SOURCES}")
add_test(NAME style_check COMMAND ${LEAN_SOURCE_DIR}/cmake/Modules/cpplint.py ${LEAN_SOURCES})

cmake_minimum_required(VERSION 3.10)
cmake_policy(SET CMP0054 NEW)
if(NOT (${CMAKE_GENERATOR} MATCHES "Unix Makefiles"))
  message(FATAL_ERROR "The only supported CMake generator at the moment is 'Unix Makefiles'")
endif()
if(NOT (DEFINED STAGE))
  message(FATAL_ERROR "STAGE must be set; use the CMakeLists.txt in the root folder")
endif()
include(ExternalProject)
project(LEAN CXX C)
set(LEAN_VERSION_MAJOR 4)
set(LEAN_VERSION_MINOR 0)
set(LEAN_VERSION_PATCH 0)
set(LEAN_VERSION_IS_RELEASE 0)  # This number is 1 in the release revision, and 0 otherwise.
set(LEAN_SPECIAL_VERSION_DESC "" CACHE STRING "Additional version description like 'nightly-2018-03-11'")
set(LEAN_VERSION_STRING "${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}.${LEAN_VERSION_PATCH}")
if (LEAN_SPECIAL_VERSION_DESC)
  string(APPEND LEAN_VERSION_STRING "-${LEAN_SPECIAL_VERSION_DESC}")
endif()

set(LEAN_EXTRA_LINKER_FLAGS "" CACHE STRING "Additional flags used by the linker")
set(LEAN_EXTRA_CXX_FLAGS "" CACHE STRING "Additional flags used by the C++ compiler")
set(LEAN_TEST_VARS "LEAN_CC=${CMAKE_C_COMPILER}" CACHE STRING "Additional environment variables used when running tests")

if (NOT CMAKE_BUILD_TYPE)
  message(STATUS "No build type selected, default to Release")
  set(CMAKE_BUILD_TYPE "Release")
endif()

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(MULTI_THREAD       "MULTI_THREAD"       ON)
option(CCACHE             "use ccache"         ON)
option(SPLIT_STACK        "SPLIT_STACK"        OFF)
# When OFF we disable LLVM support
option(LLVM               "LLVM"               OFF)
# When OFF we disable the LLVM backend
option(LLVM_BACKEND        "LLVM_BACKEND"      ON)

# When ON we include githash in the version string
option(USE_GITHASH        "GIT_HASH"           ON)
# When ON we install LICENSE files to CMAKE_INSTALL_PREFIX
option(INSTALL_LICENSE "INSTALL_LICENSE" ON)
# When ON thread storage is automatically finalized, it assumes platform support pthreads.
# This option is important when using Lean as library that is invoked from a different programming language (e.g., Haskell).
option(AUTO_THREAD_FINALIZATION "AUTO_THREAD_FINALIZATION" ON)

# FLAGS for disabling optimizations and debugging
option(FREE_VAR_RANGE_OPT  "FREE_VAR_RANGE_OPT"   ON)
option(HAS_LOCAL_OPT       "HAS_LOCAL_OPT"        ON)
option(ABSTRACTION_CACHE   "ABSTRACTION_CACHE"    ON)
option(TYPE_CLASS_CACHE    "TYPE_CLASS_CACHE"     ON)
option(TYPE_INFER_CACHE    "TYPE_INFER_CACHE"     ON)
option(ALPHA               "ALPHA FEATURES"       OFF)
option(TRACK_CUSTOM_ALLOCATORS "TRACK_CUSTOM_ALLOCATORS" OFF)
option(TRACK_LIVE_EXPRS    "TRACK_LIVE_EXPRS" OFF)
option(CUSTOM_ALLOCATORS   "CUSTOM_ALLOCATORS" ON)
option(SAVE_SNAPSHOT       "SAVE_SNAPSHOT" ON)
option(SAVE_INFO           "SAVE_INFO" ON)
option(SMALL_ALLOCATOR     "SMALL_ALLOCATOR" ON)
option(LAZY_RC             "LAZY_RC" OFF)
option(RUNTIME_STATS       "RUNTIME_STATS" OFF)
option(BSYMBOLIC "Link with -Bsymbolic to reduce call overhead in shared libraries (Linux)" ON)
option(USE_GMP "USE_GMP" ON)

# development-specific options
option(CHECK_OLEAN_VERSION "Only load .olean files compiled with the current version of Lean" ON)

set(LEAN_EXTRA_MAKE_OPTS  ""                           CACHE STRING "extra options to lean --make")
set(LEANC_CC              "cc"                         CACHE STRING "C compiler to use in `leanc`")

if ("${LAZY_RC}" MATCHES "ON")
  set(LEAN_LAZY_RC "#define LEAN_LAZY_RC")
endif()

if ("${SMALL_ALLOCATOR}" MATCHES "ON")
  set(LEAN_SMALL_ALLOCATOR "#define LEAN_SMALL_ALLOCATOR")
endif()

if(CMAKE_SIZEOF_VOID_P EQUAL 8)
  message(STATUS "64-bit machine detected")
  set(NumBits 64)
else()
  message(STATUS "32-bit machine detected")
  set(NumBits 32)
endif()

if ("${RUNTIME_STATS}" MATCHES "ON")
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_RUNTIME_STATS")
endif()

if (NOT("${CHECK_OLEAN_VERSION}" MATCHES "ON"))
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_IGNORE_OLEAN_VERSION")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
    set(MULTI_THREAD OFF)
    # TODO(WN): code size/performance tradeoffs
    # - we're using -O3; it's /okay/
    # - -flto crashes at runtime
    # - -Oz produces quite slow code
    # - system libraries such as OpenGL are included in the JS but shouldn't be
    # - we need EMSCRIPTEN_KEEPALIVE annotations on exports to run meta-dce (-s MAIN_MODULE=2)
    # - -fexceptions is a slow JS blob, remove when more runtimes support the WASM exceptions spec

    # From https://emscripten.org/docs/compiling/WebAssembly.html#backends:
    # > The simple and safe thing is to pass all -s flags at both compile and link time.
    set(EMSCRIPTEN_SETTINGS "-s ALLOW_MEMORY_GROWTH=1 -s DISABLE_EXCEPTION_CATCHING=0 -s MAIN_MODULE=1 -fexceptions")
    string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_EMSCRIPTEN ${EMSCRIPTEN_SETTINGS}")
    string(APPEND LEAN_EXTRA_LINKER_FLAGS " ${EMSCRIPTEN_SETTINGS}")
endif()
if (CMAKE_CROSSCOMPILING_EMULATOR)
  # emscripten likes to quote "node"
  string(REPLACE "\"" "" CMAKE_CROSSCOMPILING_EMULATOR ${CMAKE_CROSSCOMPILING_EMULATOR})
  # HACK(WN): lazy compilation makes Node.js startup time a bad but tolerable ~4s
  string(APPEND CMAKE_CROSSCOMPILING_EMULATOR " --wasm-lazy-compilation")
else()
  set(CMAKE_CROSSCOMPILING_EMULATOR)
endif()

# Added for CTest
include(CTest)

# Windows does not support ulimit -s unlimited. So, we reserve a lot of stack space: 100Mb
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  message(STATUS "Windows detected")
  set(LEAN_WIN_STACK_SIZE "104857600")
  if (MSVC)
    string(APPEND LEAN_EXTRA_LINKER_FLAGS " /STACK:${LEAN_WIN_STACK_SIZE}")
  else()
    string(APPEND LEAN_EXTRA_LINKER_FLAGS " -Wl,--stack,${LEAN_WIN_STACK_SIZE}")
    set(EXTRA_UTIL_LIBS ${EXTRA_UTIL_LIBS} -lpsapi)
  endif()
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_WINDOWS -D LEAN_WIN_STACK_SIZE=${LEAN_WIN_STACK_SIZE}")
  # do not import the world from windows.h using appropriately named flag
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D WIN32_LEAN_AND_MEAN")
  # DLLs must go next to executables on Windows
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
else()
  set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/lean")
endif()

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/lean")

# OSX default thread stack size is very small. Moreover, in Debug mode, each new stack frame consumes a lot of extra memory.
if ((${MULTI_THREAD} MATCHES "ON") AND (${CMAKE_SYSTEM_NAME} MATCHES "Darwin"))
  set(LEAN_EXTRA_MAKE_OPTS -s40000 ${LEAN_EXTRA_MAKE_OPTS})
endif ()

if(NOT MULTI_THREAD)
  message(STATUS "Disabled multi-thread support, it will not be safe to run multiple threads in parallel")
  set(AUTO_THREAD_FINALIZATION OFF)
else()
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_MULTI_THREAD")
endif()

if(AUTO_THREAD_FINALIZATION AND NOT MSVC)
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_AUTO_THREAD_FINALIZATION")
endif()

if(LLVM)
    # if(NOT (CMAKE_CXX_COMPILER_ID STREQUAL "Clang" AND CMAKE_C_COMPILER_ID STREQUAL "Clang"))
    # message(FATAL_ERROR "LLVM=ON must be used with clang. Set `CMAKE_CXX_COMPILER=Clang` and `CMAKE_C_COMPILER=Clang` accordingly.")
    # endif()
  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

  include_directories(${LLVM_INCLUDE_DIRS})
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_LLVM")
else()
  #message(WARNING "Disabling LLVM support.  JIT compilation will not be available")
endif()

if(LLVM_BACKEND)
    # if(NOT (CMAKE_CXX_COMPILER_ID STREQUAL "Clang" AND CMAKE_C_COMPILER_ID STREQUAL "Clang"))
    #     message(FATAL_ERROR "LLVM_BACKEND=ON must be used with clang. Set `CMAKE_CXX_COMPILER=clang++` and `CMAKE_C_COMPILER=clang` accordingly. Found ${CMAKE_CXX_COMPILER_ID}, ${CMAKE_C_COMPILER_ID}")
    # endif()
  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

  include_directories(${LLVM_INCLUDE_DIRS})
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_LLVM")
else()
  #message(WARNING "Disabling LLVM support.  JIT compilation will not be available")
endif()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "${LEAN_EXTRA_CXX_FLAGS} -DLEAN_BUILD_TYPE=\"${CMAKE_BUILD_TYPE}\" -DLEAN_EXPORTING")
set(CMAKE_CXX_FLAGS_DEBUG          "-DLEAN_DEBUG -DLEAN_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-DNDEBUG")

# SPLIT_STACK
if (SPLIT_STACK)
  if ((${CMAKE_SYSTEM_NAME} MATCHES "Linux") AND ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
     string(APPEND CMAKE_CXX_FLAGS " -fsplit-stack -D LEAN_USE_SPLIT_STACK")
     message(STATUS "Using split-stacks")
  else()
     message(FATAL_ERROR "Split-stacks are only supported on Linux with g++")
  endif()
endif()

# Compiler-specific C++14 activation.
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
    execute_process(
        COMMAND "${CMAKE_CXX_COMPILER}" -dumpversion OUTPUT_VARIABLE GCC_VERSION)
    if (NOT (GCC_VERSION VERSION_GREATER 4.9 OR GCC_VERSION VERSION_EQUAL 4.9))
        message(FATAL_ERROR "${PROJECT_NAME} requires g++ 4.9 or greater.")
    endif ()
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  string(APPEND CMAKE_CXX_FLAGS " -D__CLANG__")
elseif (MSVC)
    # All good. Maybe enforce a recent version?
    set(CMAKE_CXX_FLAGS                "/GL /EHsc /W2 /Zc:implicitNoexcept- -D_SCL_SECURE_NO_WARNINGS ${CMAKE_CXX_FLAGS}")
    set(CMAKE_CXX_FLAGS_DEBUG          "/Od /Zi ${CMAKE_CXX_FLAGS_DEBUG}")
    set(CMAKE_CXX_FLAGS_MINSIZEREL     "/Os /Zc:inline ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    set(CMAKE_CXX_FLAGS_RELEASE        "/O2 /Oi /Oy /Zc:inline ${CMAKE_CXX_FLAGS_RELEASE}")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "/O2 /Oi /Zi ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
    set(LEAN_EXTRA_LINKER_FLAGS        "/LTCG:INCREMENTAL ${LEAN_EXTRA_LINKER_FLAGS}")
    set(CMAKE_STATIC_LINKER_FLAGS      "${CMAKE_STATIC_LINKER_FLAGS} ${LEAN_EXTRA_LINKER_FLAGS}")
elseif (${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
    message(STATUS "Emscripten is detected: Make sure the wrapped compiler supports C++14")
else()
    message(FATAL_ERROR "Unsupported compiler: ${CMAKE_CXX_COMPILER_ID}")
endif ()

if (NOT MSVC)
    set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++14 ${CMAKE_CXX_FLAGS}")
    set(CMAKE_CXX_FLAGS_DEBUG          "-g3 ${CMAKE_CXX_FLAGS_DEBUG}")
    if (${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
      # smallest+slower | -Oz .. -Os .. -O3 | largest+faster
      set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Oz ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    else ()
      set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    endif ()
    set(CMAKE_CXX_FLAGS_RELEASE        "-O3 ${CMAKE_CXX_FLAGS_RELEASE}")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g3 -fno-omit-frame-pointer ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
elseif (MULTI_THREAD)
    set(CMAKE_CXX_FLAGS_DEBUG          "/MTd ${CMAKE_CXX_FLAGS_DEBUG}")
    set(CMAKE_CXX_FLAGS_MINSIZEREL     "/MT ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    set(CMAKE_CXX_FLAGS_RELEASE        "/MT ${CMAKE_CXX_FLAGS_RELEASE}")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "/MT ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
endif ()

if("${USE_GMP}" MATCHES "ON")
  set(CMAKE_CXX_FLAGS                "-D LEAN_USE_GMP ${CMAKE_CXX_FLAGS}")
  if("${CMAKE_SYSTEM_NAME}" MATCHES "Emscripten")
    include_directories(${GMP_INSTALL_PREFIX}/include)
    set(GMP_LIBRARIES "${GMP_INSTALL_PREFIX}/lib/libgmp.a")
  else()
    # GMP
    find_package(GMP 5.0.5 REQUIRED)
    include_directories(${GMP_INCLUDE_DIR})
  endif()
  if(NOT LEAN_STANDALONE)
    string(APPEND LEAN_EXTRA_LINKER_FLAGS " ${GMP_LIBRARIES}")
  endif()
endif()

# ccache
if(CCACHE AND NOT CMAKE_CXX_COMPILER_LAUNCHER AND NOT CMAKE_C_COMPILER_LAUNCHER)
  find_program(CCACHE_PATH ccache)
  if(CCACHE_PATH)
    set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_PATH}")
    set(CMAKE_C_COMPILER_LAUNCHER "${CCACHE_PATH}")
  else()
    message(WARNING "Failed to find ccache, prepare for longer and redundant builds...")
  endif()
endif()

# Python
find_package(PythonInterp)

include_directories(${CMAKE_BINARY_DIR}/include)


if (NOT LLVM_CONFIG)
    message(STATUS "'-DLLVM_CONFIG=<path/to/llvm-config>' not passed as CMake flag, finding `llvm-config` via CMake...")
    find_program(LLVM_CONFIG "llvm-config")
else()
    message(STATUS "Using given `llvm-config` '${LLVM_CONFIG}'...")
    execute_process(COMMAND ${LLVM_CONFIG} --version COMMAND_ERROR_IS_FATAL ANY)
endif()


if(NOT LLVM_CONFIG)
    message(FATAL_ERROR "Unable to find 'llvm-config'")
else()
    message(STATUS "Found 'llvm-config' as ${LLVM_CONFIG}")
endif()

# libleancpp/Lean as well as libleanrt/Init are cyclically dependent. This works by default on macOS, which also doesn't like

# the linker flags necessary on other platforms.
# Furthermore, add LLVM flags into the list of flags we need when linking.
execute_process(COMMAND ${LLVM_CONFIG}  --ldflags OUTPUT_VARIABLE LLVM_CONFIG_LDFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG}  --libs OUTPUT_VARIABLE LLVM_CONFIG_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG}  --libdir OUTPUT_VARIABLE LLVM_CONFIG_LIBDIR OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG}  --includedir OUTPUT_VARIABLE LLVM_CONFIG_INCLUDEDIR OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG}  --cxxflags OUTPUT_VARIABLE LLVM_CONFIG_CXXFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
# if we build LLVM by source (as @bollu does)<with -DBUILD_SHARED_LIBS=ON, LLVM dynamically loads system libraries
# such as '-lrt -ldl -lm -lz -ltinfo -lxml2'
execute_process(COMMAND ${LLVM_CONFIG}  --system-libs OUTPUT_VARIABLE LLVM_CONFIG_SYSTEM_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)

message("llvm-config: libdir '${LLVM_CONFIG_LIBDIR}' | ldflags '${LLVM_CONFIG_LDFLGAS}' | libs '${LLVM_CONFIG_LIBS}' | system libs '${LLVM_CONFIG_SYSTEM_LIBS}' | cxxflags: ${LLVM_CONFIG_CXXFLAGS} | includedir: ${LLVM_CONFIG_INCLUDEDIR}")

# when using shared libraries, set the `rpath` to help the dynamic loader 
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  string(APPEND LEANC_STATIC_LINKER_FLAGS " -lleancpp -lInit -lLean -lleanrt ${LLVM_CONFIG_LDFLAGS} ${LLVM_CONFIG_LIBS}")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  string(APPEND LEANC_STATIC_LINKER_FLAGS " -lleancpp -lInit -lLean -lnodefs.js -lleanrt")
else()
  string(APPEND LEANC_STATIC_LINKER_FLAGS " -Wl,--start-group -lleancpp -lLean -Wl,--end-group -Wl,--start-group -lInit -lleanrt -Wl,--end-group")
endif()

set(LEAN_CXX_STDLIB "-lstdc++" CACHE STRING "C++ stdlib linker flags")

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  set(LEAN_CXX_STDLIB "-lc++")
endif()

string(APPEND LEANC_STATIC_LINKER_FLAGS " ${LEAN_CXX_STDLIB}")
string(APPEND LEANSHARED_LINKER_FLAGS " ${LEAN_CXX_STDLIB}")

# Link LLVM for code generation
# TODO: hide this behind a flag
# Is there a guarantee that the build environment for `leanprover/lean-llvm` will match that of
# `leanprover/lean4`? Some of the system-libs as for hardcoded paths. For example:
# 
# string(APPEND LEANSHARED_LINKER_FLAGS " ${LLVM_CONFIG_LDFLAGS} ${LLVM_CONFIG_LIBS} ${LLVM_CONFIG_SYSTEM_LIBS}")
# string(APPEND LEANC_STATIC_LINKER_FLAGS " ${LLVM_CONFIG_LDFLAGS} ${LLVM_CONFIG_LIBS} ${LLVM_CONFIG_SYSTEM_LIBS}")
# for whatever reason, the system libs on macos ask for `-lm` and `-lz` which are supposedly no longer shipped
string(APPEND LEANSHARED_LINKER_FLAGS " ${LLVM_CONFIG_LDFLAGS} ${LLVM_CONFIG_LIBS} ${LLVM_CONFIG_SYSTEM_LIBS}")
set(APPEND LEAN_EXTRA_CXX_FLAGS  " ${LLVM_CONFIG_CXXFLAGS}")
# string(APPEND LEANC_STATIC_LINKER_FLAGS " ${LLVM_CONFIG_LDFLAGS} ${LLVM_CONFIG_LIBS}")

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # find_package(zstd)
    find_package(ZLIB)
    # string(APPEND LEANSHARED_LINKER_FLAGS " -L${}")
    # string(APPEND LEANSHARED_LINKER_FLAGS " -L${ZLIB_LIBRARY_PATH} -l${ZLIB_LIBRARY}")
endif()


# get rid of unused parts of C++ stdlib
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  string(APPEND LEANSHARED_LINKER_FLAGS " -Wl,-dead_strip")
else()
  string(APPEND LEANSHARED_LINKER_FLAGS " -Wl,--gc-sections")
endif()

if(NOT ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  string(APPEND LEANC_STATIC_LINKER_FLAGS " -lm")
  string(APPEND LEANSHARED_LINKER_FLAGS " -lm")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  if(BSYMBOLIC)
    string(APPEND LEANC_SHARED_LINKER_FLAGS " -Wl,-Bsymbolic")
    string(APPEND LEANSHARED_LINKER_FLAGS " -Wl,-Bsymbolic")
  endif()
  string(APPEND CMAKE_CXX_FLAGS " -fPIC -ftls-model=initial-exec")
  string(APPEND LEANC_EXTRA_FLAGS " -fPIC")
  string(APPEND LEANSHARED_LINKER_FLAGS " -Wl,-rpath=\\$$ORIGIN/..:\\$$ORIGIN")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -Wl,-rpath=\\\$ORIGIN/../lib:\\\$ORIGIN/../lib/lean")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  string(APPEND CMAKE_CXX_FLAGS " -ftls-model=initial-exec")
  string(APPEND LEANSHARED_LINKER_FLAGS " -install_name @rpath/libleanshared.dylib")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -Wl,-rpath,@executable_path/../lib -Wl,-rpath,@executable_path/../lib/lean")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " -ldl")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  find_package(ZLIB REQUIRED)
  message("ZLIB_LIBRARY: ${ZLIB_LIBRARY}")
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " ${ZLIB_LIBRARY} -lz")
endif()


if(NOT(${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  # export symbols for the interpreter (done via `LEAN_EXPORT` for Windows)
  string(APPEND LEAN_DYN_EXE_LINKER_FLAGS " -rdynamic")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -rdynamic")
  # hide all other symbols
  string(APPEND CMAKE_CXX_FLAGS " -fvisibility=hidden -fvisibility-inlines-hidden")
  string(APPEND LEANC_EXTRA_FLAGS " -fvisibility=hidden")
endif()

# On Windows, add bcrypt for random number generation
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " -lbcrypt")
endif()

# Allow `lean` symbols in plugins without linking directly against it. If we linked against the
# executable or `leanshared`, plugins would try to look them up at load time (even though they
# are already loaded) and probably fail unless we set up LD_LIBRARY_PATH.
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  # import library created by the `leanshared` target
  string(APPEND LEANC_SHARED_LINKER_FLAGS " -lleanshared")
elseif("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")
  string(APPEND LEANC_SHARED_LINKER_FLAGS " -Wl,-undefined,dynamic_lookup")
endif()
# Linux ignores undefined symbols in shared libraries by default

if(MULTI_THREAD AND NOT MSVC AND (NOT ("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")))
    string(APPEND LEAN_EXTRA_LINKER_FLAGS " -pthread")
endif()

# Git HASH
set(LEAN_PACKAGE_VERSION "NOT-FOUND")
if(USE_GITHASH)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA1)
  if(${GIT_SHA1} MATCHES "GITDIR-NOTFOUND")
    message(STATUS "Failed to read git_sha1")
    set(GIT_SHA1 "")
    if(EXISTS "${LEAN_SOURCE_DIR}/bin/package_version")
      file(STRINGS "${LEAN_SOURCE_DIR}/bin/package_version" LEAN_PACKAGE_VERSION)
      message(STATUS "Package version detected: ${LEAN_PACKAGE_VERSION}")
    endif()
  else()
    message(STATUS "git commit sha1: ${GIT_SHA1}")
  endif()
else()
  set(GIT_SHA1 "")
  if(EXISTS "${LEAN_SOURCE_DIR}/bin/package_version")
    file(STRINGS "${LEAN_SOURCE_DIR}/bin/package_version" LEAN_PACKAGE_VERSION)
    message(STATUS "Package version detected: ${LEAN_PACKAGE_VERSION}")
  endif()
endif()
configure_file("${LEAN_SOURCE_DIR}/githash.h.in" "${LEAN_BINARY_DIR}/githash.h")

# Windows uses ";" as a path separator. We use `LEAN_PATH_SEPARATOR` on scripts such as lean.mk.in
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  set(LEAN_PATH_SEPARATOR ";")
else()
  set(LEAN_PATH_SEPARATOR ":")
endif()

# Version
configure_file("${LEAN_SOURCE_DIR}/version.h.in" "${LEAN_BINARY_DIR}/include/lean/version.h")
if (${STAGE} EQUAL 0)
  set(LEAN_IS_STAGE0 "#define LEAN_IS_STAGE0 1")
else()
  set(LEAN_IS_STAGE0 "#define LEAN_IS_STAGE0 0")
endif()
configure_file("${LEAN_SOURCE_DIR}/config.h.in" "${LEAN_BINARY_DIR}/include/lean/config.h")
install(DIRECTORY ${LEAN_BINARY_DIR}/include/ DESTINATION include)
configure_file(${LEAN_SOURCE_DIR}/lean.mk.in ${LEAN_BINARY_DIR}/share/lean/lean.mk)
install(DIRECTORY ${LEAN_BINARY_DIR}/share/ DESTINATION share)

include_directories(${LEAN_SOURCE_DIR})
include_directories(${CMAKE_BINARY_DIR})  # version.h etc., "private" headers
include_directories(${CMAKE_BINARY_DIR}/include)  # config.h etc., "public" headers

string(TOUPPER "${CMAKE_BUILD_TYPE}" uppercase_CMAKE_BUILD_TYPE)
# These are used in lean.mk (and libleanrt) and passed through by stdlib.make
# They are not embedded into `leanc` since they are build profile/machine specific
string(APPEND LEANC_OPTS " ${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}}")
if(CMAKE_OSX_SYSROOT AND NOT LEAN_STANDALONE)
  string(APPEND LEANC_OPTS " ${CMAKE_CXX_SYSROOT_FLAG}${CMAKE_OSX_SYSROOT}")
endif()
if(CMAKE_OSX_DEPLOYMENT_TARGET)
  string(APPEND LEANC_OPTS " ${CMAKE_CXX_OSX_DEPLOYMENT_TARGET_FLAG}${CMAKE_OSX_DEPLOYMENT_TARGET}")
endif()

if(${STAGE} GREATER 1)
  # reuse C++ parts, which don't change
  add_library(leanrt_initial-exec STATIC IMPORTED)
  set_target_properties(leanrt_initial-exec PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/runtime/libleanrt_initial-exec.a")
  add_library(leanrt STATIC IMPORTED)
  set_target_properties(leanrt PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/lib/lean/libleanrt.a")
  add_library(leancpp STATIC IMPORTED)
  set_target_properties(leancpp PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a")
  add_custom_target(copy-leancpp
    COMMAND cmake -E copy_if_different "${PREV_STAGE}/runtime/libleanrt_initial-exec.a" "${CMAKE_BINARY_DIR}/runtime/libleanrt_initial-exec.a"
    COMMAND cmake -E copy_if_different "${PREV_STAGE}/lib/lean/libleanrt.a" "${CMAKE_BINARY_DIR}/lib/lean/libleanrt.a"
    COMMAND cmake -E copy_if_different "${PREV_STAGE}/lib/lean/libleancpp.a" "${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a")
  add_dependencies(leancpp copy-leancpp)
else()
  add_subdirectory(runtime)

  add_subdirectory(util)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:util>)
  add_subdirectory(kernel)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:kernel>)
  add_subdirectory(library)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:library>)
  add_subdirectory(library/constructions)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:constructions>)
  add_subdirectory(library/compiler)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:compiler>)
  add_subdirectory(initialize)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:initialize>)

  add_library(leancpp STATIC ${LEAN_OBJS})
  set_target_properties(leancpp PROPERTIES
    OUTPUT_NAME leancpp)
endif()

# MSYS2 bash usually handles Windows paths relatively well, but not when putting them in the PATH
string(REGEX REPLACE "^([a-zA-Z]):" "/\\1" LEAN_BIN "${CMAKE_BINARY_DIR}/bin")

# ...and Make doesn't like absolute Windows paths either
# (also looks nicer in the build log)
file(RELATIVE_PATH LIB ${LEAN_SOURCE_DIR} ${CMAKE_BINARY_DIR}/lib)

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  set(LEANSHARED_LINKER_FLAGS "-Wl,-force_load,${CMAKE_BINARY_DIR}/lib/lean/libInit.a -Wl,-force_load,${CMAKE_BINARY_DIR}/lib/lean/libLean.a -Wl,-force_load,${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a ${CMAKE_BINARY_DIR}/runtime/libleanrt_initial-exec.a ${LEANSHARED_LINKER_FLAGS}")
else()
  set(LEANSHARED_LINKER_FLAGS "-Wl,--whole-archive -lInit -lLean -lleancpp -Wl,--no-whole-archive ${CMAKE_BINARY_DIR}/runtime/libleanrt_initial-exec.a ${LEANSHARED_LINKER_FLAGS}")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    string(APPEND LEANSHARED_LINKER_FLAGS " -Wl,--out-implib,${CMAKE_BINARY_DIR}/lib/lean/libleanshared.dll.a")
  endif()
endif()

# Escape for `make`. Yes, twice.
string(REPLACE "$" "$$" CMAKE_EXE_LINKER_FLAGS_MAKE "${CMAKE_EXE_LINKER_FLAGS}")
string(REPLACE "$" "$$" CMAKE_EXE_LINKER_FLAGS_MAKE_MAKE "${CMAKE_EXE_LINKER_FLAGS_MAKE}")
configure_file(${LEAN_SOURCE_DIR}/stdlib.make.in ${CMAKE_BINARY_DIR}/stdlib.make)
add_custom_target(make_stdlib ALL
  WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
  # The actual rule is in a separate makefile because we want to prefix it with '+' to use the Make job server
  # for a parallelized nested build, but CMake doesn't let us do that.
  # We use `lean` from the previous stage, but `leanc`, headers, etc. from the current stage
  COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make Init Lean
  VERBATIM)

# We declare these as separate custom targets so they use separate `make` invocations, which makes `make` recompute which dependencies
# (e.g. `libLean.a`) are now newer than the target file

add_custom_target(leanshared ALL
  WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
  DEPENDS make_stdlib leancpp leanrt_initial-exec
  COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make leanshared
  VERBATIM)

if(${STAGE} GREATER 0)
  if(NOT EXISTS ${LEAN_SOURCE_DIR}/lake/Lake.lean)
    message(FATAL_ERROR "src/lake does not exist. Please check out the Lake submodule using `git submodule update --init src/lake`.")
  endif()

  add_custom_target(lake ALL
    WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
    DEPENDS leanshared
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make Lake
    VERBATIM)
endif()

if(PREV_STAGE)
  add_custom_target(update-stage0
    COMMAND bash -c 'CSRCS=${CMAKE_BINARY_DIR}/lib/temp script/update-stage0'
    DEPENDS make_stdlib
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/..")
endif()

# use Bash version for building, use Lean version in bin/ for tests & distribution
configure_file("${LEAN_SOURCE_DIR}/bin/leanc.in" "${CMAKE_BINARY_DIR}/leanc.sh" @ONLY)
if(${STAGE} GREATER 0 AND EXISTS ${LEAN_SOURCE_DIR}/Leanc.lean)
  configure_file("${LEAN_SOURCE_DIR}/Leanc.lean" "${CMAKE_BINARY_DIR}/leanc/Leanc.lean" @ONLY)
  add_custom_target(leanc ALL
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/leanc
    DEPENDS leanshared
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make Leanc
    VERBATIM)
endif()

file(COPY ${LEAN_SOURCE_DIR}/bin/leanmake DESTINATION ${CMAKE_BINARY_DIR}/bin)

install(DIRECTORY "${CMAKE_BINARY_DIR}/bin/" USE_SOURCE_PERMISSIONS DESTINATION bin)

add_subdirectory(shell)

add_custom_target(clean-stdlib
  COMMAND rm -rf "${CMAKE_BINARY_DIR}/lib" || true)

add_custom_target(clean-olean
  DEPENDS clean-stdlib)

install(DIRECTORY "${CMAKE_BINARY_DIR}/lib/" DESTINATION lib
  PATTERN temp EXCLUDE)

# symlink source into expected installation location for go-to-definition, if file system allows it
file(MAKE_DIRECTORY ${CMAKE_BINARY_DIR}/src)
if(${STAGE} EQUAL 0)
  file(CREATE_LINK ${CMAKE_SOURCE_DIR}/../../src ${CMAKE_BINARY_DIR}/src/lean RESULT _IGNORE_RES SYMBOLIC)
else()
  file(CREATE_LINK ${CMAKE_SOURCE_DIR} ${CMAKE_BINARY_DIR}/src/lean RESULT _IGNORE_RES SYMBOLIC)
endif()

install(DIRECTORY "${CMAKE_SOURCE_DIR}/" DESTINATION src/lean
        FILES_MATCHING
        PATTERN "*.lean"
        PATTERN "*.md"
        PATTERN examples EXCLUDE)

if(${STAGE} GREATER 0 AND INSTALL_LICENSE)
  install(FILES "${CMAKE_SOURCE_DIR}/../LICENSE" "${CMAKE_SOURCE_DIR}/../LICENSES" DESTINATION ".")
endif()

file(COPY ${CMAKE_SOURCE_DIR}/include/lean DESTINATION ${CMAKE_BINARY_DIR}/include
  FILES_MATCHING PATTERN "*.h")

set(LEAN_INSTALL_PREFIX "" CACHE STRING "If set, set CMAKE_INSTALL_PREFIX to this value + version name")
if(LEAN_INSTALL_PREFIX)
  string(TOLOWER ${CMAKE_SYSTEM_NAME} LOWER_SYSTEM_NAME)
  set(LEAN_INSTALL_SUFFIX "-${LOWER_SYSTEM_NAME}" CACHE STRING "If LEAN_INSTALL_PREFIX is set, append this value to CMAKE_INSTALL_PREFIX")
  set(CMAKE_INSTALL_PREFIX "${LEAN_INSTALL_PREFIX}/lean-${LEAN_VERSION_STRING}${LEAN_INSTALL_SUFFIX}")
endif()

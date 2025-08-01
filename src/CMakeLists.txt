cmake_minimum_required(VERSION 3.10)
cmake_policy(SET CMP0054 NEW)
cmake_policy(SET CMP0110 NEW)
if(NOT (${CMAKE_GENERATOR} MATCHES "Unix Makefiles"))
  message(FATAL_ERROR "The only supported CMake generator at the moment is 'Unix Makefiles'")
endif()
if(NOT (DEFINED STAGE))
  message(FATAL_ERROR "STAGE must be set; use the CMakeLists.txt in the root folder")
endif()
include(ExternalProject)
project(LEAN CXX C)
set(LEAN_VERSION_MAJOR 4)
set(LEAN_VERSION_MINOR 23)
set(LEAN_VERSION_PATCH 0)
set(LEAN_VERSION_IS_RELEASE 0)  # This number is 1 in the release revision, and 0 otherwise.
set(LEAN_SPECIAL_VERSION_DESC "" CACHE STRING "Additional version description like 'nightly-2018-03-11'")
set(LEAN_VERSION_STRING "${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}.${LEAN_VERSION_PATCH}")
if (LEAN_SPECIAL_VERSION_DESC)
  string(APPEND LEAN_VERSION_STRING "-${LEAN_SPECIAL_VERSION_DESC}")
elseif (NOT LEAN_VERSION_IS_RELEASE)
  string(APPEND LEAN_VERSION_STRING "-pre")
endif()
if (LEAN_VERSION_IS_RELEASE)
  set(LEAN_MANUAL_ROOT "https://lean-lang.org/doc/reference/${LEAN_VERSION_STRING}/")
else()
  set(LEAN_MANUAL_ROOT "")
endif()

set(LEAN_PLATFORM_TARGET "" CACHE STRING "LLVM triple of the target platform")
if (NOT LEAN_PLATFORM_TARGET)
  # this may fail when the compiler is not clang, but this should only happen in local builds where
  # the value of the variable is not of immediate relevance
  execute_process(COMMAND ${CMAKE_C_COMPILER} --print-target-triple
    OUTPUT_VARIABLE LEAN_PLATFORM_TARGET OUTPUT_STRIP_TRAILING_WHITESPACE)
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

# When ON we include githash in the version string
option(USE_GITHASH        "GIT_HASH"           ON)
# When ON we install LICENSE files to CMAKE_INSTALL_PREFIX
option(INSTALL_LICENSE "INSTALL_LICENSE" ON)
# When ON we install a copy of cadical
option(INSTALL_CADICAL "Install a copy of cadical" ON)

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
option(SMALL_ALLOCATOR     "SMALL_ALLOCATOR" OFF)
option(MMAP                "MMAP" ON)
option(LAZY_RC             "LAZY_RC" OFF)
option(RUNTIME_STATS       "RUNTIME_STATS" OFF)
option(BSYMBOLIC "Link with -Bsymbolic to reduce call overhead in shared libraries (Linux)" ON)
option(USE_GMP "USE_GMP" ON)
option(USE_MIMALLOC "use mimalloc" ON)

# development-specific options
option(CHECK_OLEAN_VERSION "Only load .olean files compiled with the current version of Lean" OFF)
option(USE_LAKE "Use Lake instead of lean.mk for building core libs from language server" OFF)

set(LEAN_EXTRA_MAKE_OPTS  ""                           CACHE STRING "extra options to lean --make")
set(LEANC_CC              ${CMAKE_C_COMPILER}          CACHE STRING "C compiler to use in `leanc`")

if ("${LAZY_RC}" MATCHES "ON")
  set(LEAN_LAZY_RC "#define LEAN_LAZY_RC")
endif()

if (USE_MIMALLOC)
  set(SMALL_ALLOCATOR OFF)
  set(LEAN_MIMALLOC "#define LEAN_MIMALLOC")
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

if ("${MMAP}" MATCHES "ON")
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_MMAP")
endif()

if ("${RUNTIME_STATS}" MATCHES "ON")
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_RUNTIME_STATS")
endif()

if ("${CHECK_OLEAN_VERSION}" MATCHES "ON")
  set(USE_GITHASH ON)
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_CHECK_OLEAN_VERSION")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
    # TODO(WN): code size/performance tradeoffs
    # - we're using -O3; it's /okay/
    # - -Oz produces quite slow code
    # - system libraries such as OpenGL are included in the JS but shouldn't be
    # - we need EMSCRIPTEN_KEEPALIVE annotations on exports to run meta-dce (-s MAIN_MODULE=2)

    # From https://emscripten.org/docs/compiling/WebAssembly.html#backends:
    # > The simple and safe thing is to pass all -s flags at both compile and link time.
    set(EMSCRIPTEN_SETTINGS "-s ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto")
    string(APPEND LEANC_EXTRA_CC_FLAGS " -pthread")
    string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_EMSCRIPTEN ${EMSCRIPTEN_SETTINGS}")
    string(APPEND LEAN_EXTRA_LINKER_FLAGS " ${EMSCRIPTEN_SETTINGS}")
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
  set(CMAKE_RELATIVE_LIBRARY_OUTPUT_DIRECTORY "bin")
else()
  set(CMAKE_RELATIVE_LIBRARY_OUTPUT_DIRECTORY "lib/lean")
endif()

set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/${CMAKE_RELATIVE_LIBRARY_OUTPUT_DIRECTORY}")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/lean")

# OSX default thread stack size is very small. Moreover, in Debug mode, each new stack frame consumes a lot of extra memory.
if ((${MULTI_THREAD} MATCHES "ON") AND (${CMAKE_SYSTEM_NAME} MATCHES "Darwin"))
  string(APPEND LEAN_EXTRA_MAKE_OPTS " -s40000")
endif ()

# We want explicit stack probes in huge Lean stack frames for robust stack overflow detection
string(APPEND LEANC_EXTRA_CC_FLAGS " -fstack-clash-protection")

# This makes signed integer overflow guaranteed to match 2's complement.
string(APPEND CMAKE_CXX_FLAGS " -fwrapv")
string(APPEND LEANC_EXTRA_CC_FLAGS " -fwrapv")

if(NOT MULTI_THREAD)
  message(STATUS "Disabled multi-thread support, it will not be safe to run multiple threads in parallel")
  set(AUTO_THREAD_FINALIZATION OFF)
else()
  string(APPEND LEAN_EXTRA_CXX_FLAGS " -D LEAN_MULTI_THREAD")
endif()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "${LEAN_EXTRA_CXX_FLAGS} -DLEAN_BUILD_TYPE=\"${CMAKE_BUILD_TYPE}\" -DLEAN_EXPORTING")
set(CMAKE_CXX_FLAGS_DEBUG          "-DLEAN_DEBUG")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHASSERT  "-DLEAN_DEBUG")

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
    set(CMAKE_CXX_FLAGS_RELWITHASSERT  "/O2 /Oi /Oy /Zc:inline ${CMAKE_CXX_FLAGS_RELWITHASSERT}")
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
    set(CMAKE_CXX_FLAGS_RELWITHASSERT  "-O3 ${CMAKE_CXX_FLAGS_RELWITHASSERT}")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g3 -fno-omit-frame-pointer ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
elseif (MULTI_THREAD)
    set(CMAKE_CXX_FLAGS_DEBUG          "/MTd ${CMAKE_CXX_FLAGS_DEBUG}")
    set(CMAKE_CXX_FLAGS_MINSIZEREL     "/MT ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    set(CMAKE_CXX_FLAGS_RELEASE        "/MT ${CMAKE_CXX_FLAGS_RELEASE}")
    set(CMAKE_CXX_FLAGS_RELWITHASSERT  "/MT ${CMAKE_CXX_FLAGS_RELWITHASSERT}")
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

# LibUV
if("${CMAKE_SYSTEM_NAME}" MATCHES "Emscripten")
  # Only on WebAssembly we compile LibUV ourselves
  set(LIBUV_EMSCRIPTEN_FLAGS "${EMSCRIPTEN_SETTINGS}")

  # LibUV does not compile on WebAssembly without modifications because
  # building LibUV on a platform requires including stub implementations
  # for features not present on the target platform. This patch includes
  # the minimum amount of stub implementations needed for successfully
  # running Lean on WebAssembly and using LibUV's temporary file support.
  # It still leaves several symbols completely undefined: uv__fs_event_close,
  # uv__hrtime, uv__io_check_fd, uv__io_fork, uv__io_poll, uv__platform_invalidate_fd
  # uv__platform_loop_delete, uv__platform_loop_init. Making additional
  # LibUV features available on WebAssembly might require adapting the
  # patch to include additional LibUV source files.
  set(LIBUV_PATCH_IN "
diff --git a/CMakeLists.txt b/CMakeLists.txt
index 5e8e0166..f3b29134 100644
--- a/CMakeLists.txt
+++ b/CMakeLists.txt
@@ -317,6 +317,11 @@ if(CMAKE_SYSTEM_NAME STREQUAL \"GNU\")
        src/unix/hurd.c)
 endif()

+if(CMAKE_SYSTEM_NAME STREQUAL \"Emscripten\")
+  list(APPEND uv_sources
+       src/unix/no-proctitle.c)
+endif()
+
 if(CMAKE_SYSTEM_NAME STREQUAL \"Linux\")
   list(APPEND uv_defines _GNU_SOURCE _POSIX_C_SOURCE=200112)
   list(APPEND uv_libraries dl rt)
")
  string(REPLACE "\n" "\\n" LIBUV_PATCH ${LIBUV_PATCH_IN})

  ExternalProject_add(libuv
    PREFIX libuv
    GIT_REPOSITORY https://github.com/libuv/libuv
    # Sync version with flake.nix
    GIT_TAG v1.48.0
    CMAKE_ARGS -DCMAKE_BUILD_TYPE=Release -DLIBUV_BUILD_TESTS=OFF -DLIBUV_BUILD_SHARED=OFF -DCMAKE_AR=${CMAKE_AR} -DCMAKE_TOOLCHAIN_FILE=${CMAKE_TOOLCHAIN_FILE} -DCMAKE_POSITION_INDEPENDENT_CODE=ON -DCMAKE_C_FLAGS=${LIBUV_EMSCRIPTEN_FLAGS}
	  PATCH_COMMAND git reset --hard HEAD && printf "${LIBUV_PATCH}" > patch.diff && git apply patch.diff
    BUILD_IN_SOURCE ON
    INSTALL_COMMAND "")
  set(LIBUV_INCLUDE_DIRS "${CMAKE_BINARY_DIR}/libuv/src/libuv/include")
  set(LIBUV_LDFLAGS "${CMAKE_BINARY_DIR}/libuv/src/libuv/libuv.a")
else()
  find_package(LibUV 1.0.0 REQUIRED)
endif()
include_directories(${LIBUV_INCLUDE_DIRS})
if(NOT LEAN_STANDALONE)
  string(JOIN " " LIBUV_LDFLAGS ${LIBUV_LDFLAGS})
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " ${LIBUV_LDFLAGS}")
endif()

# Windows SDK (for ICU)
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  # Pass 'tools' to skip MSVC version check (as MSVC/Visual Studio is not necessarily installed)
  find_package(WindowsSDK REQUIRED COMPONENTS tools)

  # This will give a semicolon-separated list of include directories
  get_windowssdk_include_dirs(${WINDOWSSDK_LATEST_DIR} WINDOWSSDK_INCLUDE_DIRS)

  # To successfully build against Windows SDK headers, the Windows SDK headers must have lower
  # priority than other system headers, so use `-idirafter`. Unfortunately, CMake does not
  # support this using `include_directories`.
  string(REPLACE ";" "\" -idirafter \"" WINDOWSSDK_INCLUDE_DIRS "${WINDOWSSDK_INCLUDE_DIRS}")
  string(APPEND CMAKE_CXX_FLAGS " -idirafter \"${WINDOWSSDK_INCLUDE_DIRS}\"")

  string(APPEND LEAN_EXTRA_LINKER_FLAGS " -licu")
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

# Pick up `llvm-config` to setup LLVM flags.
if(LLVM)
  if(NOT LLVM_CONFIG) # look for `llvm-config` if not supplied
    message(STATUS "'-DLLVM_CONFIG=<path/to/llvm-config>' not passed as CMake flag, finding `llvm-config` via CMake...")
    find_program(LLVM_CONFIG "llvm-config")
    if(NOT LLVM_CONFIG) # check that it was found
        message(FATAL_ERROR "Unable to find 'llvm-config'")
    endif()
  endif()
  # check that we have 'llvm-config' version.
  message(STATUS "Executing 'llvm-config --version' at '${LLVM_CONFIG}' to check configuration.")
  execute_process(COMMAND ${LLVM_CONFIG} --version COMMAND_ERROR_IS_FATAL ANY OUTPUT_VARIABLE LLVM_CONFIG_VERSION ECHO_OUTPUT_VARIABLE OUTPUT_STRIP_TRAILING_WHITESPACE)
  string(REGEX MATCH "^[0-9]*" LLVM_CONFIG_MAJOR_VERSION ${LLVM_CONFIG_VERSION})
  message(STATUS "Found 'llvm-config' at '${LLVM_CONFIG}' with version '${LLVM_CONFIG_VERSION}', major version '${LLVM_CONFIG_MAJOR_VERSION}'")
  if (NOT LLVM_CONFIG_MAJOR_VERSION STREQUAL "19")
    message(FATAL_ERROR "Unable to find llvm-config version 19. Found invalid version '${LLVM_CONFIG_MAJOR_VERSION}'")
  endif()
  # -DLEAN_LLVM is used to conditionally compile Lean features that depend on LLVM
  string(APPEND CMAKE_CXX_FLAGS " -D LEAN_LLVM")

  execute_process(COMMAND ${LLVM_CONFIG}  --ldflags OUTPUT_VARIABLE LLVM_CONFIG_LDFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
  execute_process(COMMAND ${LLVM_CONFIG}  --libs OUTPUT_VARIABLE LLVM_CONFIG_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)
  execute_process(COMMAND ${LLVM_CONFIG}  --libdir OUTPUT_VARIABLE LLVM_CONFIG_LIBDIR OUTPUT_STRIP_TRAILING_WHITESPACE)
  execute_process(COMMAND ${LLVM_CONFIG}  --includedir OUTPUT_VARIABLE LLVM_CONFIG_INCLUDEDIR OUTPUT_STRIP_TRAILING_WHITESPACE)
  execute_process(COMMAND ${LLVM_CONFIG}  --cxxflags OUTPUT_VARIABLE LLVM_CONFIG_CXXFLAGS OUTPUT_STRIP_TRAILING_WHITESPACE)
  execute_process(COMMAND ${LLVM_CONFIG}  --system-libs OUTPUT_VARIABLE LLVM_CONFIG_SYSTEM_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)
  message(STATUS "llvm-config: libdir '${LLVM_CONFIG_LIBDIR}' | ldflags '${LLVM_CONFIG_LDFLAGS}' | libs '${LLVM_CONFIG_LIBS}' | system libs '${LLVM_CONFIG_SYSTEM_LIBS}' | cxxflags: ${LLVM_CONFIG_CXXFLAGS} | includedir: ${LLVM_CONFIG_INCLUDEDIR}")
else()
  message(WARNING "Disabling LLVM support")
endif()

# libleancpp/Lean as well as libleanrt/Init are cyclically dependent. This works by default on macOS, which also doesn't like
# the linker flags necessary on other platforms.
# Furthermore, add LLVM flags into the list of flags we need when linking.
# when using shared libraries, set the `rpath` to help the dynamic loader
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  if(LLVM) # link to Zlib because LLVM depends on it.
    find_package(ZLIB REQUIRED)
    message(STATUS "ZLIB_LIBRARY: ${ZLIB_LIBRARY}")
    cmake_path(GET ZLIB_LIBRARY PARENT_PATH ZLIB_LIBRARY_PARENT_PATH)
    string(APPEND LEANSHARED_LINKER_FLAGS " -L ${ZLIB_LIBRARY_PARENT_PATH}")
  endif()
  string(APPEND TOOLCHAIN_STATIC_LINKER_FLAGS " -lleancpp -lInit -lStd -lLean -lleanrt")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  string(APPEND TOOLCHAIN_STATIC_LINKER_FLAGS " -lleancpp -lInit -lStd -lLean -lnodefs.js -lleanrt")
else()
  string(APPEND TOOLCHAIN_STATIC_LINKER_FLAGS " -Wl,--start-group -lleancpp -lLean -Wl,--end-group -lStd -Wl,--start-group -lInit -lleanrt -Wl,--end-group")
endif()

set(LEAN_CXX_STDLIB "-lstdc++" CACHE STRING "C++ stdlib linker flags")

if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  set(LEAN_CXX_STDLIB "-lc++")
endif()

string(APPEND TOOLCHAIN_STATIC_LINKER_FLAGS " ${LEAN_CXX_STDLIB}")
string(APPEND TOOLCHAIN_SHARED_LINKER_FLAGS " ${LEAN_CXX_STDLIB}")

# in local builds, link executables and not just dynlibs against C++ stdlib as well,
# which is required for e.g. asan
if(NOT LEAN_STANDALONE)
  string(APPEND CMAKE_EXE_LINKER_FLAGS " ${LEAN_CXX_STDLIB}")
endif()

# flags for user binaries = flags for toolchain binaries + Lake
set(LEANC_STATIC_LINKER_FLAGS " ${TOOLCHAIN_STATIC_LINKER_FLAGS} -lLake")
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  set(LEANC_SHARED_LINKER_FLAGS " ${TOOLCHAIN_SHARED_LINKER_FLAGS} -Wl,--as-needed -lLake_shared -Wl,--no-as-needed")
else()
  set(LEANC_SHARED_LINKER_FLAGS " ${TOOLCHAIN_SHARED_LINKER_FLAGS} -lLake_shared")
endif()

if (LLVM)
  string(APPEND LEANSHARED_LINKER_FLAGS " -L${LLVM_CONFIG_LIBDIR} ${LLVM_CONFIG_LDFLAGS} ${LLVM_CONFIG_LIBS} ${LLVM_CONFIG_SYSTEM_LIBS}")
  string(APPEND CMAKE_CXX_FLAGS " -I${LLVM_CONFIG_INCLUDEDIR}")
endif()

if(LLVM AND ${STAGE} GREATER 0)
    # Here, we perform a replacement of `llvm-host` with `llvm`. This is necessary for our cross-compile
    #   builds in `script/prepare-llvm-*.sh`.
    # - Recall that the host's copy of LLVM binaries and libraries is at
    #   `llvm-host`, and the target's copy of LLVM binaries and libraries is at
    #   `llvm`.
    # - In an ideal world, we would run the target's `llvm/bin/llvm-config` and get the correct link options for the target
    #   (e.g. `-Lllvm/lib/libLLVM`.)
    # - However, the target's `llvm/bin/llvm-config` has a different target
    #   triple from the host, and thus cannot be run on the host.
    # - So, we run the host `llvm-host/bin/llvm-config` from which we pick up
    #   compiler options, and change the output of the host to point to the target.
    # - In particular, `host/bin/llvm-config` produces flags like `-Lllvm-host/lib/libLLVM`, while
    #   we need the path to be `-Lllvm/lib/libLLVM`. Thus, we perform this replacement here.
    string(REPLACE "llvm-host" "llvm" LEANSHARED_LINKER_FLAGS ${LEANSHARED_LINKER_FLAGS})
    string(REPLACE "llvm-host" "llvm" LEAN_EXTRA_CXX_FLAGS ${LEAN_EXTRA_CXX_FLAGS})
    message(VERBOSE "leanshared linker flags: '${LEANSHARED_LINKER_FLAGS}' | lean extra cxx flags '${LEAN_EXTR_CXX_FLAGS}'")
endif()

# get rid of unused parts of C++ stdlib
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  string(APPEND TOOLCHAIN_SHARED_LINKER_FLAGS " -Wl,-dead_strip")
elseif(NOT ${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  string(APPEND TOOLCHAIN_SHARED_LINKER_FLAGS " -Wl,--gc-sections")
endif()

if(NOT ${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " -lm")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  if(BSYMBOLIC)
    string(APPEND LEANC_SHARED_LINKER_FLAGS " -Wl,-Bsymbolic")
    string(APPEND TOOLCHAIN_SHARED_LINKER_FLAGS " -Wl,-Bsymbolic")
  endif()
  string(APPEND CMAKE_CXX_FLAGS " -fPIC -ftls-model=initial-exec")
  string(APPEND LEANC_EXTRA_CC_FLAGS " -fPIC")
  string(APPEND TOOLCHAIN_SHARED_LINKER_FLAGS " -Wl,-rpath=\\$$ORIGIN/..:\\$$ORIGIN")
  string(APPEND LAKESHARED_LINKER_FLAGS " -Wl,--whole-archive ${CMAKE_BINARY_DIR}/lib/lean/libLake.a.export -Wl,--no-whole-archive")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -Wl,-rpath=$ORIGIN/../lib:$ORIGIN/../lib/lean")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  string(APPEND CMAKE_CXX_FLAGS " -ftls-model=initial-exec")
  string(APPEND INIT_SHARED_LINKER_FLAGS " -install_name @rpath/libInit_shared.dylib")
  string(APPEND LEANSHARED_1_LINKER_FLAGS " -install_name @rpath/libleanshared_1.dylib")
  string(APPEND LEANSHARED_LINKER_FLAGS " -install_name @rpath/libleanshared.dylib")
  string(APPEND LAKESHARED_LINKER_FLAGS " -Wl,-force_load,${CMAKE_BINARY_DIR}/lib/lean/libLake.a.export -install_name @rpath/libLake_shared.dylib")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -Wl,-rpath,@executable_path/../lib -Wl,-rpath,@executable_path/../lib/lean")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  string(APPEND CMAKE_CXX_FLAGS " -fPIC")
  string(APPEND LEANC_EXTRA_CC_FLAGS " -fPIC")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  string(APPEND LAKESHARED_LINKER_FLAGS " -Wl,--out-implib,${CMAKE_BINARY_DIR}/lib/lean/libLake_shared.dll.a -Wl,--whole-archive ${CMAKE_BINARY_DIR}/lib/lean/libLake.a.export -Wl,--no-whole-archive")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " -ldl")
endif()

if(NOT(${CMAKE_SYSTEM_NAME} MATCHES "Windows") AND NOT(${CMAKE_SYSTEM_NAME} MATCHES "Emscripten"))
  # export symbols for the interpreter (done via `LEAN_EXPORT` for Windows)
  string(APPEND LEAN_DYN_EXE_LINKER_FLAGS " -rdynamic")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -rdynamic")
  # hide all other symbols
  string(APPEND CMAKE_CXX_FLAGS " -fvisibility=hidden -fvisibility-inlines-hidden")
  string(APPEND LEANC_EXTRA_CC_FLAGS " -fvisibility=hidden")
endif()

# On Windows, add bcrypt for random number generation
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " -lbcrypt")
endif()

# Allow `lean` symbols in plugins without linking directly against it. If we linked against the
# executable or `leanshared`, plugins would try to look them up at load time (even though they
# are already loaded) and probably fail unless we set up LD_LIBRARY_PATH.
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  # import libraries created by the stdlib.make targets
  string(APPEND LEANC_SHARED_LINKER_FLAGS " -lInit_shared -lleanshared_1 -lleanshared")
elseif("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")
  # The second flag is necessary to even *load* dylibs without resolved symbols, as can happen
  # if a Lake `extern_lib` depends on a symbols defined by the Lean library but is loaded even
  # before definition.
  string(APPEND LEANC_SHARED_LINKER_FLAGS " -Wl,-undefined,dynamic_lookup -Wl,-no_fixup_chains")
endif()
# Linux ignores undefined symbols in shared libraries by default

if(MULTI_THREAD AND NOT MSVC AND (NOT ("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")))
    string(APPEND LEAN_EXTRA_LINKER_FLAGS " -pthread")
endif()

# Git HASH
if(USE_GITHASH)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA1 ALLOW_LOOKING_ABOVE_CMAKE_SOURCE_DIR)
  if(${GIT_SHA1} MATCHES "GITDIR-NOTFOUND")
    message(STATUS "Failed to read git_sha1")
    set(GIT_SHA1 "")
  else()
    message(STATUS "git commit sha1: ${GIT_SHA1}")
  endif()
else()
  if(USE_LAKE AND ${STAGE} EQUAL 0)
    # we need to embed *some* hash for Lake to invalidate stage 1 on stage 0 changes
    execute_process(
        COMMAND git ls-tree HEAD "${CMAKE_CURRENT_SOURCE_DIR}/../../stage0" --object-only
        OUTPUT_VARIABLE GIT_SHA1
        OUTPUT_STRIP_TRAILING_WHITESPACE)
    message(STATUS "stage0 sha1: ${GIT_SHA1}")
    # Now that we've prepared the information for the next stage, we can forget that we will use
    # Lake in the future as we won't use it in this stage
    set(USE_LAKE OFF)
  else()
    set(GIT_SHA1 "")
  endif()
endif()
configure_file("${LEAN_SOURCE_DIR}/githash.h.in" "${LEAN_BINARY_DIR}/githash.h")

if(USE_LAKE AND ${STAGE} EQUAL 0)
  # Now that we've prepared the information for the next stage, we can forget that we will use
  # Lake in the future as we won't use it in this stage
  set(USE_LAKE OFF)
endif()

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
if (USE_MIMALLOC)
  file(COPY "${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/include/mimalloc.h" DESTINATION "${LEAN_BINARY_DIR}/include/lean")
endif()
install(DIRECTORY ${LEAN_BINARY_DIR}/include/ DESTINATION include)
configure_file(${LEAN_SOURCE_DIR}/lean.mk.in ${LEAN_BINARY_DIR}/share/lean/lean.mk)
install(DIRECTORY ${LEAN_BINARY_DIR}/share/ DESTINATION share)

include_directories(${LEAN_SOURCE_DIR})
include_directories(${CMAKE_BINARY_DIR})  # version.h etc., "private" headers
include_directories(${CMAKE_BINARY_DIR}/include)  # config.h etc., "public" headers

# Lean code only needs this one include
string(APPEND LEANC_OPTS " -I${CMAKE_BINARY_DIR}/include")

# Use CMake profile C++ flags for building Lean libraries, but do not embed in `leanc`
string(TOUPPER "${CMAKE_BUILD_TYPE}" uppercase_CMAKE_BUILD_TYPE)
string(APPEND LEANC_OPTS " ${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}}")

# Do embed flag for finding system headers and libraries in dev builds
if(CMAKE_OSX_SYSROOT AND NOT LEAN_STANDALONE)
  string(APPEND LEANC_EXTRA_CC_FLAGS " ${CMAKE_CXX_SYSROOT_FLAG}${CMAKE_OSX_SYSROOT}")
  string(APPEND LEAN_EXTRA_LINKER_FLAGS " ${CMAKE_CXX_SYSROOT_FLAG}${CMAKE_OSX_SYSROOT}")
endif()

add_subdirectory(initialize)
add_subdirectory(shell)
# to be included in `leanshared` but not the smaller `leanshared_1` (as it would pull
# in the world)
add_library(leaninitialize STATIC $<TARGET_OBJECTS:initialize>)
set_target_properties(leaninitialize PROPERTIES
  ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib/temp
  OUTPUT_NAME leaninitialize)
add_library(leanshell STATIC util/shell.cpp)
set_target_properties(leanshell PROPERTIES
  ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib/temp
  OUTPUT_NAME leanshell)
if (${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -Wl,--whole-archive -lleanmanifest -Wl,--no-whole-archive")
endif()

if(${STAGE} GREATER 1)
  # reuse C++ parts, which don't change
  add_library(leanrt_initial-exec STATIC IMPORTED)
  set_target_properties(leanrt_initial-exec PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/runtime/libleanrt_initial-exec.a")
  add_library(leanrt STATIC IMPORTED)
  set_target_properties(leanrt PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/lib/lean/libleanrt.a")
  add_library(leancpp_1 STATIC IMPORTED)
  set_target_properties(leancpp_1 PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/lib/temp/libleancpp_1.a")
  add_library(leancpp STATIC IMPORTED)
  set_target_properties(leancpp PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a")
  add_custom_target(copy-leancpp
    COMMAND cmake -E copy_if_different "${PREV_STAGE}/runtime/libleanrt_initial-exec.a" "${CMAKE_BINARY_DIR}/runtime/libleanrt_initial-exec.a"
    COMMAND cmake -E copy_if_different "${PREV_STAGE}/lib/lean/libleanrt.a" "${CMAKE_BINARY_DIR}/lib/lean/libleanrt.a"
    COMMAND cmake -E copy_if_different "${PREV_STAGE}/lib/lean/libleancpp.a" "${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a"
    COMMAND cmake -E copy_if_different "${PREV_STAGE}/lib/temp/libleancpp_1.a" "${CMAKE_BINARY_DIR}/lib/temp/libleancpp_1.a")
  add_dependencies(leancpp copy-leancpp)
  if(LLVM)
      add_custom_target(copy-lean-h-bc
        COMMAND cmake -E copy_if_different "${PREV_STAGE}/lib/lean/lean.h.bc" "${CMAKE_BINARY_DIR}/lib/lean/lean.h.bc")
      add_dependencies(leancpp copy-lean-h-bc)
  endif()
else()
  add_subdirectory(runtime)
  if("${CMAKE_SYSTEM_NAME}" MATCHES "Emscripten")
    add_dependencies(leanrt libuv)
    add_dependencies(leanrt_initial-exec libuv)
  endif()

  add_subdirectory(util)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:util>)
  add_subdirectory(kernel)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:kernel>)
  add_subdirectory(library)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:library>)
  add_subdirectory(library/constructions)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:constructions>)

  # leancpp without `initialize` (see `leaninitialize` above)
  add_library(leancpp_1 STATIC ${LEAN_OBJS})
  set_target_properties(leancpp_1 PROPERTIES
    ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib/temp
    OUTPUT_NAME leancpp_1)
  add_library(leancpp STATIC ${LEAN_OBJS} $<TARGET_OBJECTS:initialize>)
  set_target_properties(leancpp PROPERTIES
    OUTPUT_NAME leancpp)
endif()

if((${STAGE} GREATER 0) AND CADICAL AND INSTALL_CADICAL)
  add_custom_target(copy-cadical
    COMMAND cmake -E copy_if_different "${CADICAL}" "${CMAKE_BINARY_DIR}/bin/cadical${CMAKE_EXECUTABLE_SUFFIX}")
  add_dependencies(leancpp copy-cadical)
endif()

# MSYS2 bash usually handles Windows paths relatively well, but not when putting them in the PATH
string(REGEX REPLACE "^([a-zA-Z]):" "/\\1" LEAN_BIN "${CMAKE_BINARY_DIR}/bin")

# ...and Make doesn't like absolute Windows paths either
# (also looks nicer in the build log)
file(RELATIVE_PATH LIB ${LEAN_SOURCE_DIR} ${CMAKE_BINARY_DIR}/lib)

if (${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  # We do not use dynamic linking via leanshared for Emscripten to keep things
  # simple. (And we are not interested in `Lake` anyway.) To use dynamic
  # linking, we would probably have to set MAIN_MODULE=2 on `leanshared`,
  # SIDE_MODULE=2 on `lean`, and set CMAKE_SHARED_LIBRARY_SUFFIX to ".js".
  # We set `ERROR_ON_UNDEFINED_SYMBOLS=0` because our build of LibUV does not
  # define all symbols, see the comment about LibUV on WebAssembly further up
  # in this file.
  string(APPEND LEAN_EXE_LINKER_FLAGS " ${LIB}/temp/libleanshell.a ${TOOLCHAIN_STATIC_LINKER_FLAGS} ${EMSCRIPTEN_SETTINGS} -lnodefs.js -s EXIT_RUNTIME=1 -s MAIN_MODULE=1 -s LINKABLE=1 -s EXPORT_ALL=1 -s ERROR_ON_UNDEFINED_SYMBOLS=0")
endif()

# Build the compiler using the bootstrapped C sources for stage0, and use
# the LLVM build for stage1 and further.
if (LLVM AND ${STAGE} GREATER 0)
  set(EXTRA_LEANMAKE_OPTS "LLVM=1")
endif()

set(STDLIBS Init Std Lean Leanc)
if(NOT ${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  list(APPEND STDLIBS Lake)
endif()

add_custom_target(make_stdlib ALL
  WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
  # The actual rule is in a separate makefile because we want to prefix it with '+' to use the Make job server
  # for a parallelized nested build, but CMake doesn't let us do that.
  # We use `lean` from the previous stage, but `leanc`, headers, etc. from the current stage
  COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make ${STDLIBS}
  VERBATIM)

# if we have LLVM enabled, then build `lean.h.bc` which has the LLVM bitcode
# of Lean runtime to be built.
if (LLVM AND ${STAGE} EQUAL 1)
   add_dependencies(make_stdlib runtime_bc)
endif()

# We declare these as separate custom targets so they use separate `make` invocations, which makes `make` recompute which dependencies
# (e.g. `libLean.a`) are now newer than the target file

if(${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  # dummy targets, see `MAIN_MODULE` discussion above
  add_custom_target(Init_shared ALL
    DEPENDS make_stdlib leanrt_initial-exec
    COMMAND touch ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/libInit_shared${CMAKE_SHARED_LIBRARY_SUFFIX}
  )
  add_custom_target(leanshared ALL
    DEPENDS Init_shared leancpp
    COMMAND touch ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/libleanshared_1${CMAKE_SHARED_LIBRARY_SUFFIX}
    COMMAND touch ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/libleanshared${CMAKE_SHARED_LIBRARY_SUFFIX}
  )
  add_custom_target(lake_shared ALL
    DEPENDS leanshared
    COMMAND touch ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/libLake_shared${CMAKE_SHARED_LIBRARY_SUFFIX}
  )
else()
  add_custom_target(Init_shared ALL
    WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
    DEPENDS make_stdlib leanrt_initial-exec
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make Init_shared
    VERBATIM)

  add_custom_target(leanshared ALL
    WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
    DEPENDS Init_shared leancpp_1 leancpp leanshell leaninitialize
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make leanshared
    VERBATIM)

  string(APPEND CMAKE_EXE_LINKER_FLAGS " -lInit_shared -lleanshared_1 -lleanshared")
endif()

if(NOT ${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  add_custom_target(lake_shared
    WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
    DEPENDS leanshared
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make libLake_shared
    VERBATIM)
  add_custom_target(lake ALL
    WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
    DEPENDS lake_shared
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make lake
    VERBATIM)
endif()

if(PREV_STAGE)
  add_custom_target(update-stage0
    COMMAND bash -c 'CSRCS=${CMAKE_BINARY_DIR}/lib/temp script/lib/update-stage0'
    DEPENDS make_stdlib
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/..")

  add_custom_target(update-stage0-commit
    COMMAND git commit -m "chore: update stage0"
    DEPENDS update-stage0)
endif()

# use Bash version for building, use Lean version in bin/ for tests & distribution
configure_file("${LEAN_SOURCE_DIR}/bin/leanc.in" "${CMAKE_BINARY_DIR}/leanc.sh" @ONLY)
if(${STAGE} GREATER 0 AND EXISTS ${LEAN_SOURCE_DIR}/Leanc.lean AND NOT ${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  configure_file("${LEAN_SOURCE_DIR}/Leanc.lean" "${CMAKE_BINARY_DIR}/leanc/Leanc.lean" @ONLY)
  add_custom_target(leanc ALL
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/leanc
    DEPENDS leanshared
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make leanc
    VERBATIM)
endif()

file(COPY ${LEAN_SOURCE_DIR}/bin/leanmake DESTINATION ${CMAKE_BINARY_DIR}/bin)

install(DIRECTORY "${CMAKE_BINARY_DIR}/bin/" USE_SOURCE_PERMISSIONS DESTINATION bin)

if (${STAGE} GREATER 0 AND CADICAL AND INSTALL_CADICAL)
  install(PROGRAMS "${CADICAL}" DESTINATION bin)
endif()

add_custom_target(clean-stdlib
  COMMAND rm -rf "${CMAKE_BINARY_DIR}/lib" || true)

add_custom_target(clean-olean
  DEPENDS clean-stdlib)

install(DIRECTORY "${CMAKE_BINARY_DIR}/lib/" DESTINATION lib
  PATTERN temp EXCLUDE
  PATTERN "*.export" EXCLUDE
  PATTERN "*.hash" EXCLUDE
  PATTERN "*.trace" EXCLUDE
  PATTERN "*.rsp" EXCLUDE)

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

if (STAGE GREATER 1)
  # The build of stage2+ may depend on local changes made to src/ that are not reflected by the
  # commit hash in stage1/bin/lean, so we make sure to disable the global cache
  string(APPEND LEAN_EXTRA_LAKEFILE_TOML "\n\nenableArtifactCache = false")
endif()

# Escape for `make`. Yes, twice.
string(REPLACE "$" "\\\$$" CMAKE_EXE_LINKER_FLAGS_MAKE "${CMAKE_EXE_LINKER_FLAGS}")
configure_file(${LEAN_SOURCE_DIR}/stdlib.make.in ${CMAKE_BINARY_DIR}/stdlib.make)

# hacky
function(toml_escape IN OUTVAR)
  if(IN)
    string(STRIP "${IN}" OUT)
    string(REPLACE " " "\", \"" OUT "${OUT}")
    set(${OUTVAR} "\"${OUT}\"" PARENT_SCOPE)
  endif()
endfunction()
string(REPLACE "ROOT" "${CMAKE_BINARY_DIR}" LEANC_CC "${LEANC_CC}")
string(REPLACE "ROOT" "${CMAKE_BINARY_DIR}" LEANC_INTERNAL_FLAGS "${LEANC_INTERNAL_FLAGS}")
string(REPLACE "ROOT" "${CMAKE_BINARY_DIR}" LEANC_INTERNAL_LINKER_FLAGS "${LEANC_INTERNAL_LINKER_FLAGS}")
set(LEANC_OPTS_TOML "${LEANC_OPTS} ${LEANC_EXTRA_CC_FLAGS} ${LEANC_INTERNAL_FLAGS}")
set(LINK_OPTS_TOML "${LEANC_INTERNAL_LINKER_FLAGS} -L${CMAKE_BINARY_DIR}/lib/lean ${LEAN_EXTRA_LINKER_FLAGS}")

toml_escape("${LEAN_EXTRA_MAKE_OPTS}" LEAN_EXTRA_OPTS_TOML)
toml_escape("${LEANC_OPTS_TOML}" LEANC_OPTS_TOML)
toml_escape("${LINK_OPTS_TOML}" LINK_OPTS_TOML)

if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  set(LAKE_LIB_PREFIX "lib")
endif()

if(USE_LAKE)
  configure_file(${LEAN_SOURCE_DIR}/lakefile.toml.in ${CMAKE_BINARY_DIR}/lakefile.toml)
  # copy for editing
  if(STAGE EQUAL 1)
    configure_file(${LEAN_SOURCE_DIR}/lakefile.toml.in ${LEAN_SOURCE_DIR}/lakefile.toml)
  endif()
endif()

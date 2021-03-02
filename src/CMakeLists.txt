cmake_minimum_required(VERSION 3.10)
cmake_policy(SET CMP0054 NEW)
if(NOT (${CMAKE_GENERATOR} MATCHES "Unix Makefiles"))
  message(FATAL_ERROR "The only supported CMake generator at the moment is 'Unix Makefiles'")
endif()
if(NOT (DEFINED STAGE))
  message(FATAL_ERROR "STAGE must be set; use the CMakeLists.txt in the root folder")
endif()
project(LEAN CXX C)
set(LEAN_VERSION_MAJOR 4)
set(LEAN_VERSION_MINOR 0)
set(LEAN_VERSION_PATCH 0)
set(LEAN_VERSION_IS_RELEASE 0)  # This number is 1 in the release revision, and 0 otherwise.
set(LEAN_SPECIAL_VERSION_DESC "" CACHE STRING "Additional version description like 'nightly-2018-03-11'")
set(LEAN_VERSION_STRING "${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}.${LEAN_VERSION_PATCH}")
if (LEAN_SPECIAL_VERSION_DESC)
  set(LEAN_VERSION_STRING "${LEAN_VERSION_STRING}-${LEAN_SPECIAL_VERSION_DESC}")
endif()

set(LEAN_EXTRA_LINKER_FLAGS "" CACHE STRING "Additional flags used by the linker")
set(LEAN_EXTRA_CXX_FLAGS "" CACHE STRING "Additional flags used by the C++ compiler")

if (NOT CMAKE_BUILD_TYPE)
  message(STATUS "No build type selected, default to Release")
  set(CMAKE_BUILD_TYPE "Release")
endif()

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(MULTI_THREAD       "MULTI_THREAD"       ON)
option(CCACHE             "use ccache"         ON)
option(STATIC             "STATIC"             OFF)
option(SPLIT_STACK        "SPLIT_STACK"        OFF)
# When OFF we disable LLVM support
option(LLVM               "LLVM"               OFF)
option(COMPRESSED_OBJECT_HEADER "Use compressed object headers in 64-bit machines, this option is ignored in 32-bit machines, and assumes the 64-bit OS can only address 2^48 bytes" ON)
option(SMALL_RC "Use only 32-bits for RC, this option is only relevant when COMPRESSED_OBJECT_HEARDER is ON" ON)
option(CHECK_RC_OVERFLOW "Check for RC overflows when SMALL_RC is ON" OFF)

# Include MSYS2 required DLLs and binaries in the binary distribution package
option(INCLUDE_MSYS2_DLLS "INCLUDE_MSYS2_DLLS" OFF)
# When ON we include githash in the version string
option(USE_GITHASH        "GIT_HASH"           ON)
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
option(FAKE_FREE           "Disable actually freeing runtime objects, useful for debugging memory management issues" OFF)
option(SMALL_ALLOCATOR     "SMALL_ALLOCATOR" ON)
option(LAZY_RC             "LAZY_RC" OFF)
option(RUNTIME_STATS       "RUNTIME_STATS" OFF)

# development-specific options
option(CHECK_OLEAN_VERSION "Only load .olean files compiled with the current version of Lean" ON)

set(LEAN_EXTRA_MAKE_OPTS  ""                           CACHE STRING "extra options to lean --make")
set(MINGW_LOCAL_DIR       "C:/msys64/mingw64/bin"      CACHE STRING "where to find MSYS2 required DLLs and binaries")

if ("${FAKE_FREE}" MATCHES "ON")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_FAKE_FREE")
endif()

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

if ("${COMPRESSED_OBJECT_HEADER}" MATCHES "ON")
  if (NumBits EQUAL "64")
    if ("${SMALL_RC}" MATCHES "ON")
        set(LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC "#define LEAN_COMPRESSED_OBJECT_HEADER_SMALL_RC")
        message(STATUS "Using compressed object headers and only 32-bits for reference counter, this feature assume the OS only uses memory addresses < 2^48")
        if ("${CHECK_RC_OVERFLOW}" MATCHES "ON")
           set(LEAN_CHECK_RC_OVERFLOW "#define LEAN_CHECK_RC_OVERFLOW")
           message(STATUS "RC overflow checks are enabled")
        endif()
    else()
        set(LEAN_COMPRESSED_OBJECT_HEADER "#define LEAN_COMPRESSED_OBJECT_HEADER")
        message(STATUS "Using compressed object headers, this feature assume the OS only uses memory addresses < 2^48")
    endif()
  else()
    message(STATUS "Compressed object headers cannot be used in 32-bit machines")
  endif()
else()
    message(STATUS "Using big object headers")
endif()

if ("${RUNTIME_STATS}" MATCHES "ON")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_RUNTIME_STATS")
endif()

if (NOT("${CHECK_OLEAN_VERSION}" MATCHES "ON"))
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_IGNORE_OLEAN_VERSION")
endif()

if("${CMAKE_C_COMPILER}" MATCHES "emcc")
    set(EMSCRIPTEN ON)
    set(MULTI_THREAD OFF)
    set(TCMALLOC OFF)
    set(CFLAGS_EMSCRIPTEN "-Oz -O3")
    set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} ${CFLAGS_EMSCRIPTEN} -D LEAN_EMSCRIPTEN")
    set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} --memory-init-file 0 --llvm-lto 1 -s ALLOW_MEMORY_GROWTH=1 -s DISABLE_EXCEPTION_CATCHING=0 ${CFLAGS_EMSCRIPTEN}")
    set(LEAN_JS_LIBRARY "${CMAKE_CURRENT_SOURCE_DIR}" CACHE STRING "location of olean files for lean.js")
endif()
if (CMAKE_CROSSCOMPILING_EMULATOR)
  # emscripten likes to quote "node"
  string(REPLACE "\"" "" CMAKE_CROSSCOMPILING_EMULATOR ${CMAKE_CROSSCOMPILING_EMULATOR})
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
    set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} /STACK:${LEAN_WIN_STACK_SIZE}")
  else()
    set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -Wl,--stack,${LEAN_WIN_STACK_SIZE}")
    set(LEANC_EXTRA_FLAGS "${LEANC_EXTRA_FLAGS} -Wl,--stack,${LEAN_WIN_STACK_SIZE}")
    set(EXTRA_UTIL_LIBS ${EXTRA_UTIL_LIBS} -lpsapi)
  endif()
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_WINDOWS -D LEAN_WIN_STACK_SIZE=${LEAN_WIN_STACK_SIZE}")
endif()

# OSX default thread stack size is very small. Moreover, in Debug mode, each new stack frame consumes a lot of extra memory.
if ((${MULTI_THREAD} MATCHES "ON") AND (${CMAKE_SYSTEM_NAME} MATCHES "Darwin"))
  set(LEAN_EXTRA_MAKE_OPTS -s40000 ${LEAN_EXTRA_MAKE_OPTS})
endif ()

if(NOT MULTI_THREAD)
  message(STATUS "Disabled multi-thread support, it will not be safe to run multiple threads in parallel")
  set(AUTO_THREAD_FINALIZATION OFF)
else()
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_MULTI_THREAD")
endif()

if(AUTO_THREAD_FINALIZATION AND NOT MSVC)
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_AUTO_THREAD_FINALIZATION")
endif()

if(LLVM)
  find_package(LLVM REQUIRED CONFIG)
  message(STATUS "Found CLANG ${CLANG_PACKAGE_VERSION}")
  message(STATUS "Using ClangConfig.cmake in: ${CLANG_DIR}")
  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

  include_directories(${LLVM_INCLUDE_DIRS})
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_LLVM")

  # Find the libraries that correspond to the LLVM components
  #   that we wish to use and define llvm_libs
  llvm_map_components_to_libnames(llvm_libs nativecodegen)
else()
  #message(WARNING "Disabling LLVM support.  JIT compilation will not be available")
endif()

if(STATIC)
  # Creating a fully static executable is a bad idea in general when linking against libc and specifically
  # with our dlopen shenanigans
  message(STATUS "Linking libraries statically where possible")
  if(NOT "${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")
    set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -static-libgcc -static-libstdc++")
  endif()
  set(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
  if (MULTI_THREAD AND ${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -Wl,-Bstatic,--whole-archive -lwinpthread -Wl,--no-whole-archive,-Bdynamic")
  endif()
endif()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "${LEAN_EXTRA_CXX_FLAGS} -DLEAN_BUILD_TYPE=\"${CMAKE_BUILD_TYPE}\"")
set(CMAKE_CXX_FLAGS_DEBUG          "-DLEAN_DEBUG -DLEAN_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-DNDEBUG")

# SPLIT_STACK
if (SPLIT_STACK)
  if ((${CMAKE_SYSTEM_NAME} MATCHES "Linux") AND ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
     set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsplit-stack -D LEAN_USE_SPLIT_STACK")
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
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D__CLANG__")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # In OSX, clang requires "-stdlib=libc++" to support C++14
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
    set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -stdlib=libc++")
  endif ()
elseif (MSVC)
    # All good. Maybe enforce a recent version?
    set(STATIC ON) # FIXME: not working yet
    set(CMAKE_CXX_FLAGS                "/GL /EHsc /W2 /Zc:implicitNoexcept- -D_SCL_SECURE_NO_WARNINGS ${CMAKE_CXX_FLAGS}")
    set(CMAKE_CXX_FLAGS_DEBUG          "/Od /Zi ${CMAKE_CXX_FLAGS_DEBUG}")
    set(CMAKE_CXX_FLAGS_MINSIZEREL     "/Os /Zc:inline ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    set(CMAKE_CXX_FLAGS_RELEASE        "/O2 /Oi /Oy /Zc:inline ${CMAKE_CXX_FLAGS_RELEASE}")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "/O2 /Oi /Zi ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
    set(LEAN_EXTRA_LINKER_FLAGS        "/LTCG:INCREMENTAL ${LEAN_EXTRA_LINKER_FLAGS}")
    set(CMAKE_STATIC_LINKER_FLAGS      "${CMAKE_STATIC_LINKER_FLAGS} ${LEAN_EXTRA_LINKER_FLAGS}")
elseif (EMSCRIPTEN)
    message(STATUS "Emscripten is detected: Make sure the wraped compiler supports C++14")
else()
    message(FATAL_ERROR "Unsupported compiler: ${CMAKE_CXX_COMPILER_ID}")
endif ()

if (NOT MSVC)
    set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++14 ${CMAKE_CXX_FLAGS}")
    set(CMAKE_CXX_FLAGS_DEBUG          "-g3 ${CMAKE_CXX_FLAGS_DEBUG}")
    set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    set(CMAKE_CXX_FLAGS_RELEASE        "-O3 ${CMAKE_CXX_FLAGS_RELEASE}")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g3 -fno-omit-frame-pointer ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
elseif (MULTI_THREAD)
    set(CMAKE_CXX_FLAGS_DEBUG          "/MTd ${CMAKE_CXX_FLAGS_DEBUG}")
    set(CMAKE_CXX_FLAGS_MINSIZEREL     "/MT ${CMAKE_CXX_FLAGS_MINSIZEREL}")
    set(CMAKE_CXX_FLAGS_RELEASE        "/MT ${CMAKE_CXX_FLAGS_RELEASE}")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "/MT ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
endif ()

if (EMSCRIPTEN)
    set(gmp_install_prefix ${CMAKE_CURRENT_BINARY_DIR}/gmp-root)
    # The plethory of configure arguments only makes sure that gmp thinks sizeof(mp_limb_t) == sizeof(long) == 4
    ExternalProject_Add(
            gmp
            URL https://gmplib.org/download/gmp/gmp-6.1.1.tar.bz2
            URL_HASH SHA256=a8109865f2893f1373b0a8ed5ff7429de8db696fc451b1036bd7bdf95bbeffd6
            BUILD_IN_SOURCE 1
            CONFIGURE_COMMAND emconfigure ./configure "CC_FOR_BUILD=gcc" "CCAS=gcc -c" "CFLAGS=-m32 -DPIC ${CFLAGS_EMSCRIPTEN}" --host=x86_64-pc-linux-gnu --build=i686-pc-linux-gnu --disable-assembly --prefix=${gmp_install_prefix}
            BUILD_COMMAND emmake make -j4
            INSTALL_COMMAND make install
    )
    add_library(lean_external_deps INTERFACE)
    target_link_libraries(lean_external_deps INTERFACE ${gmp_install_prefix}/lib/libgmp.so)
    include_directories(lean_external_deps INTERFACE ${gmp_install_prefix}/include)
    add_dependencies(lean_external_deps gmp)
    set(EXTRA_LIBS lean_external_deps)
else()
    # GMP
    find_package(GMP 5.0.5 REQUIRED)
    include_directories(${GMP_INCLUDE_DIR})
    set(COPY_LIBS ${COPY_LIBS} ${GMP_LIBRARIES})
    # dlopen
    set(EXTRA_LIBS ${EXTRA_LIBS} ${CMAKE_DL_LIBS})
endif()

# ccache
if(CCACHE)
  find_program(CCACHE_PATH ccache)
  if(CCACHE_PATH)
    set(CMAKE_CXX_COMPILER_LAUNCHER "${CCACHE_PATH}")
    set(CMAKE_C_COMPILER_LAUNCHER "${CCACHE_PATH}")
  else()
    message(WARNING "Failed to find ccache, prepare for longer and redundant builds...")
  endif()
endif()

set(EXTRA_LIBS ${EXTRA_LIBS} ${COPY_LIBS})

# Python
find_package(PythonInterp)

include_directories(${CMAKE_BINARY_DIR}/include)

# libleancpp and the stdlib libraries are cyclically dependent. This works by default on macOS, which also doesn't like
# the linker flags necessary on other platforms.
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  set(LEANC_STATIC_LINKER_FLAGS "-lleancpp -lInit -lStd -lLean")
else()
  # `-pie` defaulting is not consistent on Linux distributions, so let's default to off
  set(LEANC_STATIC_LINKER_FLAGS "-no-pie -Wl,--start-group -lleancpp -lInit -lStd -lLean -Wl,--end-group")
endif()

if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  set(LEANC_SHARED_LINKER_FLAGS "${LEANC_SHARED_LINKER_FLAGS} -fPIC")
endif()

# export all symbols for the interpreter
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LEAN_EXTRA_LINKER_FLAGS} -Wl,--export-all")
  set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--export-all")
  set(LEANC_SHARED_LINKER_FLAGS "${LEANC_SHARED_LINKER_FLAGS} -Wl,--export-all")
else()
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LEAN_EXTRA_LINKER_FLAGS} -rdynamic")
  set(LEANC_EXTRA_FLAGS "${LEANC_EXTRA_FLAGS} -ldl")
endif()

# Allow `lean` symbols in plugins without linking directly against it. If we linked against the
# executable or `leanshared`, plugins would try to look them up at load time (even though they
# are already loaded) and probably fail unless we set up LD_LIBRARY_PATH.
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  # import library created by the `lean` target
  set(LEANC_SHARED_LINKER_FLAGS "$bindir/lean.exe.a")
elseif("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")
  set(LEANC_SHARED_LINKER_FLAGS "${LEANC_EXTRA_FLAGS} -Wl,-undefined,dynamic_lookup")
endif()
# Linux ignores undefined symbols in shared libraries by default

if(MULTI_THREAD AND NOT MSVC AND (NOT ("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")))
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread")
    set(LEANC_EXTRA_FLAGS "${LEANC_EXTRA_FLAGS} -pthread")
endif()

# Git HASH
set(LEAN_PACKAGE_VERSION "NOT-FOUND")
if(USE_GITHASH)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA1)
  if(${GIT_SHA1} MATCHES "GITDIR-NOTFOUND")
    message(STATUS "Failed to read git_sha1")
    if(EXISTS "${LEAN_SOURCE_DIR}/bin/package_version")
      file(STRINGS "${LEAN_SOURCE_DIR}/bin/package_version" LEAN_PACKAGE_VERSION)
      message(STATUS "Package version detected: ${LEAN_PACKAGE_VERSION}")
    endif()
  else()
    message(STATUS "git commit sha1: ${GIT_SHA1}")
  endif()
else()
  set(GIT_SHA1 "GITDIR-NOTFOUND")
  if(EXISTS "${LEAN_SOURCE_DIR}/bin/package_version")
    file(STRINGS "${LEAN_SOURCE_DIR}/bin/package_version" LEAN_PACKAGE_VERSION)
    message(STATUS "Package version detected: ${LEAN_PACKAGE_VERSION}")
  endif()
endif()
configure_file("${LEAN_SOURCE_DIR}/githash.h.in" "${LEAN_BINARY_DIR}/githash.h")

# Version
configure_file("${LEAN_SOURCE_DIR}/version.h.in" "${LEAN_BINARY_DIR}/include/lean/version.h")
if (${STAGE} EQUAL 0)
  set(LEAN_IS_STAGE0 "#define LEAN_IS_STAGE0 1")
else()
  set(LEAN_IS_STAGE0 "#define LEAN_IS_STAGE0 0")
endif()
configure_file("${LEAN_SOURCE_DIR}/config.h.in" "${LEAN_BINARY_DIR}/include/lean/config.h")
install(DIRECTORY ${LEAN_BINARY_DIR}/include/lean DESTINATION include)
configure_file(${LEAN_SOURCE_DIR}/lean.mk.in ${LEAN_BINARY_DIR}/share/lean/lean.mk)
install(DIRECTORY ${LEAN_BINARY_DIR}/share/lean DESTINATION share)

if(EMSCRIPTEN)
    set(LEAN_LIBRARY_TYPE SHARED)
else()
   set(LEAN_LIBRARY_TYPE STATIC)
endif()

include_directories(${LEAN_SOURCE_DIR})
include_directories(${CMAKE_BINARY_DIR})  # version.h etc., "private" headers
include_directories(${CMAKE_BINARY_DIR}/include)  # config.h etc., "public" headers

if(LEANCPP)
  add_library(leancpp STATIC IMPORTED)
  set_target_properties(leancpp PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a")
  add_custom_target(copy-leancpp
    COMMAND cmake -E copy_if_different "${LEANCPP}" "${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a")
  add_dependencies(leancpp copy-leancpp)
else()
  add_subdirectory(runtime)
  set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:runtime>)
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
  if(${STAGE} EQUAL 0)
    add_subdirectory(../stdlib stdlib)
    set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:stage0>)
  endif()

  add_library(leancpp ${LEAN_LIBRARY_TYPE} ${LEAN_OBJS})
  set_target_properties(leancpp PROPERTIES
    ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib/lean"
    OUTPUT_NAME leancpp)
endif()
install(FILES ${CMAKE_BINARY_DIR}/lib/lean/libleancpp.a DESTINATION lib/lean)

# MSYS2 bash usually handles Windows paths relatively well, but not when putting them in the PATH
string(REGEX REPLACE "^([a-zA-Z]):" "/\\1" LEAN_BIN "${CMAKE_BINARY_DIR}/bin")

# make stdlib using previous stage
if(PREV_STAGE)
  # ...and Make doesn't like absolute Windows paths either
  # (also looks nicer in the build log)
  file(RELATIVE_PATH LIB ${LEAN_SOURCE_DIR} ${CMAKE_BINARY_DIR}/lib)

  string(TOUPPER "${CMAKE_BUILD_TYPE}" uppercase_CMAKE_BUILD_TYPE)
  set(LEANC_OPTS "${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}}")

  configure_file(${LEAN_SOURCE_DIR}/stdlib.make.in ${CMAKE_BINARY_DIR}/stdlib.make)
  add_custom_target(make_stdlib ALL
    WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
    # The actual rule is in a separate makefile because we want to prefix it with '+' to use the Make job server
    # for a parallelized nested build, but CMake doesn't let us do that.
    # We use `lean` from the previous stage, but `leanc`, headers, etc. from the current stage
    COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make)

  add_library(Init STATIC IMPORTED)
  set_target_properties(Init PROPERTIES
    IMPORTED_LOCATION ${CMAKE_BINARY_DIR}/lib/lean/libInit.a)
  add_dependencies(Init make_stdlib)

  add_library(Std STATIC IMPORTED)
  set_target_properties(Std PROPERTIES
    IMPORTED_LOCATION ${CMAKE_BINARY_DIR}/lib/lean/libStd.a)
  add_dependencies(Std make_stdlib)

  add_library(Lean STATIC IMPORTED)
  set_target_properties(Lean PROPERTIES
    IMPORTED_LOCATION ${CMAKE_BINARY_DIR}/lib/lean/libLean.a)
  add_dependencies(Lean make_stdlib)

  # leancpp and the Lean libs are cyclically dependent
  target_link_libraries(Init INTERFACE leancpp)
  target_link_libraries(Std INTERFACE leancpp Init)
  target_link_libraries(Lean INTERFACE leancpp Std Init)
  target_link_libraries(leancpp INTERFACE Init Std Lean)

  add_custom_target(update-stage0
    COMMAND cmake -E env LIB=${CMAKE_BINARY_DIR}/lib bash script/update-stage0
    DEPENDS make_stdlib
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/..")
endif()

target_link_libraries(leancpp INTERFACE ${EXTRA_LIBS})
if(LLVM)
  target_link_libraries(leancpp INTERFACE ${llvm_libs})
endif()

configure_file("${LEAN_SOURCE_DIR}/bin/leanc.in" "${CMAKE_BINARY_DIR}/bin/leanc" @ONLY)
install(FILES "${CMAKE_BINARY_DIR}/bin/leanc"
  DESTINATION bin
  PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)
file(COPY ${LEAN_SOURCE_DIR}/bin/leanmake DESTINATION ${CMAKE_BINARY_DIR}/bin)
install(FILES ${LEAN_SOURCE_DIR}/bin/leanmake
  DESTINATION bin
  PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)
install(FILES "${CMAKE_BINARY_DIR}/bin/leanpkg${CMAKE_EXECUTABLE_SUFFIX}"
  DESTINATION bin
  PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)

# shared library deactivated until we figure out the leancpp/Init story
# # The DLL (shared library) is not being generated correctly when we use cross-compilation (i.e., generate the Windows DLL using Linux).
# # For some strange reason, it contains a copy of pthread_equal.
# # Remark: this problem does not happen when we generate the DLL using msys2 on Windows.
# if (NOT("${CROSS_COMPILE}" MATCHES "ON"))
#   if ("${STATIC}" MATCHES "OFF")
#     add_library(leanshared SHARED shared/init.cpp)
#     # see `target_link_libraries(lean ...)`
#     target_link_libraries(leanshared leancpp Init leancpp Init)
#     install(TARGETS leanshared DESTINATION lib)
#   endif()
# endif()

add_subdirectory(shell)

add_custom_target(clean-stdlib
  COMMAND rm -rf "${CMAKE_BINARY_DIR}/lib" || true)

add_custom_target(clean-olean
  DEPENDS clean-stdlib)

install(DIRECTORY "${CMAKE_BINARY_DIR}/lib/lean" DESTINATION lib)

install(DIRECTORY "${CMAKE_SOURCE_DIR}" DESTINATION lib/lean
        FILES_MATCHING
        PATTERN "*.lean"
        PATTERN "*.md")

file(COPY ${CMAKE_SOURCE_DIR}/include/lean DESTINATION ${CMAKE_BINARY_DIR}/include
  FILES_MATCHING PATTERN "*.h")

if("${INCLUDE_MSYS2_DLLS}" MATCHES "ON")
  # TODO(Leo): do not hardcode required DLLs.
  # For example, we can try to use ldd to retrieve the list of required DLLs.
  set(RUNTIME_LIBRARIES
         ${MINGW_LOCAL_DIR}/libgmp-10.dll
         ${MINGW_LOCAL_DIR}/libwinpthread-1.dll
         ${MINGW_LOCAL_DIR}/libgcc_s_seh-1.dll
         ${MINGW_LOCAL_DIR}/libstdc++-6.dll)
  install(PROGRAMS ${RUNTIME_LIBRARIES} DESTINATION bin)
endif()

# CPack
set(CPACK_PACKAGE_NAME lean)
set(CPACK_PACKAGE_CONTACT "Leonardo de Moura <leodemoura@microsoft.com>")
string(TOLOWER ${CMAKE_SYSTEM_NAME} LOWER_SYSTEM_NAME)
string(TIMESTAMP COMPILE_DATETIME "%Y%m%d%H%M%S")
set(CPACK_PACKAGE_VERSION "${LEAN_VERSION_STRING}.${COMPILE_DATETIME}")
if(NOT (${GIT_SHA1} MATCHES "GITDIR-NOTFOUND"))
  set(CPACK_PACKAGE_VERSION "${CPACK_PACKAGE_VERSION}.git${GIT_SHA1}")
endif()
set(CPACK_PACKAGE_FILE_NAME "lean-${LEAN_VERSION_STRING}-${LOWER_SYSTEM_NAME}")
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  SET(CPACK_GENERATOR TGZ)
else()
  SET(CPACK_GENERATOR ZIP)
endif()
# CPack -- Debian
if(STATIC)
  SET(CPACK_DEBIAN_PACKAGE_DEPENDS "")
else()
  SET(CPACK_DEBIAN_PACKAGE_DEPENDS "libstdc++-4.8-dev,libgmp-dev")
endif()
SET(CPACK_DEBIAN_PACKAGE_DESCRIPTION "Lean Theorem Prover")
SET(CPACK_DEBIAN_PACKAGE_SECTION "devel")
include(CPack)

cmake_minimum_required(VERSION 2.8.7)
project(LEAN CXX C)
set(LEAN_VERSION_MAJOR 0)
set(LEAN_VERSION_MINOR 3)
set(LEAN_VERSION_PATCH 0)

set(LEAN_EXTRA_LINKER_FLAGS "")
set(LEAN_EXTRA_CXX_FLAGS "")

if("${CMAKE_C_COMPILER}" MATCHES "emcc")
    set(EMSCRIPTEN ON)
    set(CROSS_COMPILE ON)
    set(IGNORE_SORRY ON)
    set(MULTI_THREAD OFF)
    set(TCMALLOC OFF)
    set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_EMSCRIPTEN")
    set(LEAN_JS_LIBRARY "${CMAKE_CURRENT_SOURCE_DIR}/../library" CACHE STRING
            "location of olean files for lean.js")
endif()

if (NOT CMAKE_BUILD_TYPE)
  message(STATUS "No build type selected, default to Release")
  set(CMAKE_BUILD_TYPE "Release")
endif()

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(MULTI_THREAD       "MULTI_THREAD"       ON)
option(STATIC             "STATIC"             OFF)
option(SPLIT_STACK        "SPLIT_STACK"        OFF)
option(READLINE           "READLINE"           OFF)
option(TCMALLOC           "TCMALLOC"           ON)
option(JEMALLOC           "JEMALLOC"           OFF)
# When ON we enable the lean-server support used for IDEs
option(SERVER             "SERVER"             ON)

# IGNORE_SORRY is a tempory option (hack). It allows us to build
# a version of Lean that does not report when 'sorry' is used.
# This is useful for suppressing warning messages in the nightly builds.
option(IGNORE_SORRY       "IGNORE_SORRY"      OFF)
# When cross-compiling, we do not compile the standard library since
# the executable will not work on the host machine
option(CROSS_COMPILE      "CROSS_COMPILE"     OFF)
# When ON we try to minimize the amount of memory needed to compile Lean using gcc.
# We use this flag when compiling at Travis.
option(CONSERVE_MEMORY    "CONSERVE_MEMORY"   OFF)
# Include MSYS2 required DLLs and binaries in the binary distribution package
option(INCLUDE_MSYS2_DLLS "INCLUDE_MSYS2_DLLS" OFF)
# When ON we include githash in the version string
option(USE_GITHASH        "GIT_HASH"          ON)
# When ON thread storage is automatically finalized, it assumes platform support pthreads.
# This option is important when using Lean as library that is invoked from a different programming language (e.g., Haskell).
option(AUTO_THREAD_FINALIZATION "AUTO_THREAD_FINALIZATION" ON)

# emacs site-lisp dir
set(EMACS_LISP_DIR        "share/emacs/site-lisp/lean" CACHE STRING "emacs site-lisp dir")
# library dir
set(LIBRARY_DIR           "lib/lean"                   CACHE STRING "library dir")
set(LEAN_EXT_INCLUDE_DIR  "include/lean_ext"           CACHE STRING "include dir for building Lean extensions")
set(LEAN_EXTRA_MAKE_OPTS  ""                           CACHE STRING "extra options to lean --make")

message(STATUS "Lean emacs-mode will be installed at "
  "${CMAKE_INSTALL_PREFIX}/${EMACS_LISP_DIR}")
message(STATUS "Lean library will be installed at "
  "${CMAKE_INSTALL_PREFIX}/${LIBRARY_DIR}")

# Added for CTest
include(CTest)
configure_file("${LEAN_SOURCE_DIR}/CTestCustom.cmake.in"
  "${LEAN_BINARY_DIR}/CTestCustom.cmake" @ONLY)

# Windows does not support ulimit -s unlimited. So, we reserve a lot of stack space: 100Mb
if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  message(STATUS "Windows detected")
  set(LEAN_WIN_STACK_SIZE "104857600")
  set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -Wl,--stack,${LEAN_WIN_STACK_SIZE}")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_WINDOWS -D LEAN_WIN_STACK_SIZE=${LEAN_WIN_STACK_SIZE}")
  set(EXTRA_LIBS ${EXTRA_LIBS} -lpsapi)
endif()

if("${CYGWIN}" EQUAL "1")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_CYGWIN")
endif()

if("${SERVER}" MATCHES "ON")
  message(STATUS "Compile server enabled")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_SERVER")
endif()

if(MINGW AND CMAKE_COMPILER_IS_GNUCXX)
  # See https://github.com/leanprover/lean/issues/930#issuecomment-172555475
  message(STATUS "Set _GLIBCXX_USE_CXX11_ABI = 0 for a system using MSYS2 + g++")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D_GLIBCXX_USE_CXX11_ABI=0")
endif()

if(NOT MULTI_THREAD)
  message(STATUS "Disabled multi-thread support, it will not be safe to run multiple threads in parallel")
  set(AUTO_THREAD_FINALIZATION OFF)
else()
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_MULTI_THREAD")
endif()

if(AUTO_THREAD_FINALIZATION)
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_AUTO_THREAD_FINALIZATION")
endif()

if(CONSERVE_MEMORY AND ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
  message(STATUS "Using compilation flags for minimizing the amount of memory used by gcc")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} --param ggc-min-heapsize=32768 --param ggc-min-expand=20")
endif()

if(STATIC)
  message(STATUS "Creating a static executable")
  if (MULTI_THREAD AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux")
    set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -Wl,--whole-archive -lpthread -Wl,--no-whole-archive")
  endif()
  set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -static")
endif()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${LEAN_EXTRA_CXX_FLAGS} -DLEAN_BUILD_TYPE=\"${CMAKE_BUILD_TYPE}\"")
set(CMAKE_CXX_FLAGS_DEBUG          "-g3 -DLEAN_DEBUG -DLEAN_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g3")
set(CMAKE_CXX_FLAGS_GPROF          "-O2 -g -pg")
set(CMAKE_CXX_FLAGS_EMSCRIPTEN     "-Oz -O3 -s ALLOW_MEMORY_GROWTH=1 --llvm-lto 1 -s DISABLE_EXCEPTION_CATCHING=0 -Wno-warn-absolute-paths")

# OSX .dmg generation (this is working in progress)
set(CPACK_DMG_BACKGROUND_IMAGE "${LEAN_SOURCE_DIR}/../images/lean.png")
set(CPACK_DMG_VOLUME_NAME "Lean-${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}")
set(CPACK_BUNDLE_NAME "Lean-${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}")
set(CPACK_BUNDLE_STARTUP_COMMAND "bin/leanemacs")
set(CPACK_PACKAGE_FILE_NAME "Lean-${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}")
set(CPACK_PACKAGE_ICON "${LEAN_SOURCE_DIR}/../images/lean.png")
##################

# Set a consistent MACOSX_RPATH default across all CMake versions.
# When CMake 2.8.12 is required, change this default to 1.
# When CMake 3.0.0 is required, remove this block (see CMP0042).
if (NOT DEFINED CMAKE_MACOSX_RPATH)
  set(CMAKE_MACOSX_RPATH 0)
endif()

if (${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  # The following options is needed to generate a shared library
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")
endif()

include(CheckIncludeFileCXX)
check_include_file_cxx("unistd.h" HAVE_UNISTD)

if (IGNORE_SORRY)
  message(STATUS "IGNORE_SORRY is ON, Lean will not report when 'sorry' is used directly or indirectly")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D LEAN_IGNORE_SORRY")
endif()

# SPLIT_STACK
if (SPLIT_STACK)
  if ((${CMAKE_SYSTEM_NAME} MATCHES "Linux") AND ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
     set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsplit-stack -D LEAN_USE_SPLIT_STACK")
     message(STATUS "Using split-stacks")
  else()
     message(FATAL_ERROR "Split-stacks are only supported on Linux with g++")
  endif()
endif()

# Test coverage
if(TESTCOV)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} --coverage")
endif()

# Compiler-specific C++11 activation.
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
    execute_process(
        COMMAND "${CMAKE_CXX_COMPILER}" -dumpversion OUTPUT_VARIABLE GCC_VERSION)
    if (NOT (GCC_VERSION VERSION_GREATER 4.8 OR GCC_VERSION VERSION_EQUAL 4.8))
        message(FATAL_ERROR "${PROJECT_NAME} requires g++ 4.8 or greater.")
    endif ()
elseif ("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D__CLANG__")
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
    # In OSX, clang requires "-stdlib=libc++" to support C++11
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
    set(LEAN_EXTRA_LINKER_FLAGS "-stdlib=libc++")
  endif ()
elseif (EMSCRIPTEN)
    message(STATUS "Emscripten is detected: Make sure the wraped compiler supports C++11")
else()
    message(FATAL_ERROR "Your C++ compiler does not support C++11.")
endif ()

if (${EMSCRIPTEN})
    include(ExternalProject)
    set(gmp_install_prefix ${CMAKE_CURRENT_BINARY_DIR}/gmp-root)
    # The plethory of configure arguments only makes sure that gmp thinks sizeof(mp_limb_t) == sizeof(long) == 4
    ExternalProject_Add(
            gmp
            URL https://gmplib.org/download/gmp/gmp-6.1.1.tar.bz2
            URL_HASH SHA256=a8109865f2893f1373b0a8ed5ff7429de8db696fc451b1036bd7bdf95bbeffd6
            BUILD_IN_SOURCE 1
            CONFIGURE_COMMAND emconfigure ./configure CFLAGS=-m32\ -DPIC --build=i686-pc-linux-gnu --disable-assembly --prefix=${gmp_install_prefix}
            BUILD_COMMAND emmake make -j4
            INSTALL_COMMAND make install
    )
    set(mpfr_install_prefix ${CMAKE_CURRENT_BINARY_DIR}/mpfr-root)
    ExternalProject_Add(
            mpfr
            DEPENDS gmp
            URL http://www.mpfr.org/mpfr-current/mpfr-3.1.5.tar.bz2
            URL_HASH SHA256=ca498c1c7a74dd37a576f353312d1e68d490978de4395fa28f1cbd46a364e658
            BUILD_IN_SOURCE 1
            CONFIGURE_COMMAND emconfigure ./configure --prefix=${mpfr_install_prefix} --with-gmp-include=${gmp_install_prefix}/include --with-gmp-lib=${gmp_install_prefix}/lib
            BUILD_COMMAND emmake make -j4
            INSTALL_COMMAND make install
    )

    add_library(lean_external_deps INTERFACE)
    target_link_libraries(lean_external_deps INTERFACE ${gmp_install_prefix}/lib/libgmp.so ${mpfr_install_prefix}/lib/libmpfr.so)
    include_directories(lean_external_deps INTERFACE ${gmp_install_prefix}/include ${mpfr_install_prefix}/include)
    add_dependencies(lean_external_deps gmp mpfr)
    set(EXTRA_LIBS lean_external_deps)
else()
    # MPFR
    find_package(MPFR 3.1.0 REQUIRED)
    include_directories(${MPFR_INCLUDES})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${MPFR_LIBRARIES})

    # GMP
    find_package(GMP 5.0.5 REQUIRED)
    include_directories(${GMP_INCLUDE_DIR})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${GMP_LIBRARIES})
endif()

# DL
if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  # TODO(Jared): config dlopen windows support
else()
  set(EXTRA_LIBS ${EXTRA_LIBS} dl)
endif()

# TRACK_MEMORY_USAGE
if(TRACK_MEMORY_USAGE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D LEAN_TRACK_MEMORY")
endif()

# jemalloc
if(JEMALLOC)
  find_package(Jemalloc)
  if(${JEMALLOC_FOUND})
    set(EXTRA_LIBS ${EXTRA_LIBS} ${JEMALLOC_LIBRARIES})
    message(STATUS "Using jemalloc.")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D HAS_JEMALLOC")
  else()
    message(STATUS "Failed to find jemalloc, will try tcmalloc and then standard malloc.")
  endif()
endif()

# tcmalloc
if(NOT "${JEMALLOC_FOUND}")
 if(TCMALLOC)
   find_package(Tcmalloc)
   if(${TCMALLOC_FOUND})
     set(EXTRA_LIBS ${EXTRA_LIBS} ${TCMALLOC_LIBRARIES})
     message(STATUS "Using tcmalloc.")
     set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D HAS_TCMALLOC")
   else()
     message(STATUS "Failed to find tcmalloc, using standard malloc.")
   endif()
 else()
   message(STATUS "Using standard malloc.")
 endif()
endif()

# Readline
if(READLINE)
  find_package(Readline)
  set(EXTRA_LIBS ${EXTRA_LIBS} ${READLINE_LIBRARY})
  message(STATUS "Using GNU readline")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DLEAN_USE_READLINE")
endif()

# Python
find_package(PythonInterp)

include_directories(${LEAN_SOURCE_DIR})

# Git HASH
set(LEAN_PACKAGE_VERSION "NOT-FOUND")
if(USE_GITHASH)
  include(GetGitRevisionDescription)
  get_git_head_revision(GIT_REFSPEC GIT_SHA1)
  if(${GIT_SHA1} MATCHES "GITDIR-NOTFOUND")
    message(STATUS "Failed to read git_sha1")
    if(EXISTS "${LEAN_SOURCE_DIR}/../bin/package_version")
      file(STRINGS "${LEAN_SOURCE_DIR}/../bin/package_version" LEAN_PACKAGE_VERSION)
      message(STATUS "Package version detected: ${LEAN_PACKAGE_VERSION}")
    endif()
  else()
    message(STATUS "git commit sha1: ${GIT_SHA1}")
  endif()
else()
  set(GIT_SHA1 "GITDIR-NOTFOUND")
  if(EXISTS "${LEAN_SOURCE_DIR}/../bin/package_version")
    file(STRINGS "${LEAN_SOURCE_DIR}/../bin/package_version" LEAN_PACKAGE_VERSION)
    message(STATUS "Package version detected: ${LEAN_PACKAGE_VERSION}")
  endif()
endif()
configure_file("${LEAN_SOURCE_DIR}/githash.h.in" "${LEAN_BINARY_DIR}/githash.h")

# Version
configure_file("${LEAN_SOURCE_DIR}/version.h.in" "${LEAN_BINARY_DIR}/version.h")

# leanemacs file
configure_file("${LEAN_SOURCE_DIR}/../bin/leanemacs.in" "${LEAN_SOURCE_DIR}/../bin/leanemacs")
configure_file("${LEAN_SOURCE_DIR}/../bin/leanemacs.bat.in" "${LEAN_SOURCE_DIR}/../bin/leanemacs.bat")

include_directories("${LEAN_BINARY_DIR}")
add_subdirectory(util)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:util>)
add_subdirectory(util/numerics)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:numerics>)
add_subdirectory(util/sexpr)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:sexpr>)
add_subdirectory(util/interval)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:interval>)
add_subdirectory(util/lp)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:lp>)
add_subdirectory(kernel)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:kernel>)
add_subdirectory(kernel/inductive)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:inductive>)
add_subdirectory(kernel/quotient)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:quotient>)
add_subdirectory(library)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:library>)
add_subdirectory(library/tactic)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:tactic>)
add_subdirectory(library/tactic/backward)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:backward>)
add_subdirectory(library/tactic/congruence)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:congruence>)
add_subdirectory(library/constructions)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:constructions>)
add_subdirectory(library/equations_compiler)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:equations_compiler>)
add_subdirectory(library/inductive_compiler)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:inductive_compiler>)
add_subdirectory(library/vm)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:vm>)
add_subdirectory(library/compiler)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:compiler>)
add_subdirectory(library/native_compiler)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:native_compiler>)
add_subdirectory(frontends/lean)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:lean_frontend>)
add_subdirectory(frontends/smt2)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:smt2_frontend>)
add_subdirectory(init)
set(LEAN_OBJS ${LEAN_OBJS} $<TARGET_OBJECTS:init>)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LEAN_EXTRA_LINKER_FLAGS}")
if(MULTI_THREAD AND (NOT ("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")))
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread")
endif()
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")
if(EMSCRIPTEN)
    set(LEAN_LIBRARY_TYPE SHARED)
else()
   set(LEAN_LIBRARY_TYPE STATIC)
endif()
add_library(leanstatic ${LEAN_LIBRARY_TYPE} ${LEAN_OBJS})
target_link_libraries(leanstatic ${EXTRA_LIBS})
if ((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -Wl,--export-all")
endif()
add_subdirectory(api)
# The DLL (shared library) is not being generated correctly when we use cross-compilation (i.e., generate the Windows DLL using Linux).
# For some strange reason, it contains a copy of pthread_equal.
# Remark: this problem does not happen when we generate the DLL using msys2 on Windows.
if (NOT("${CROSS_COMPILE}" MATCHES "ON"))
  add_library(leanshared SHARED shared/init.cpp $<TARGET_OBJECTS:api> ${LEAN_OBJS})
  target_link_libraries(leanshared ${EXTRA_LIBS})
  install(TARGETS leanshared DESTINATION lib)
  install(TARGETS leanstatic DESTINATION lib)
endif()

add_subdirectory(shell)
add_subdirectory(emacs)

function(add_exec_test name tgt)
    if(${EMSCRIPTEN})
        target_link_libraries(${tgt} "--memory-init-file 0")
        add_test(NAME ${name} COMMAND node ${CMAKE_CURRENT_BINARY_DIR}/${tgt}.js)
    else()
        add_test(NAME ${name} COMMAND ${CMAKE_CURRENT_BINARY_DIR}/${tgt})
    endif()
endfunction()

add_subdirectory(tests/util)
add_subdirectory(tests/util/numerics)
add_subdirectory(tests/util/interval)
add_subdirectory(tests/kernel)
add_subdirectory(tests/library)
add_subdirectory(tests/frontends/lean)
add_subdirectory(tests/shell)

# Compatibility Checks using https://github.com/foonathan/compatibility
set(COMP_CMAKE_PATH "${CMAKE_SOURCE_DIR}/cmake/Modules" CACHE INTERNAL "")
include(CompBase)
if(NOT EMSCRIPTEN)
  # This test does not work when compiling with emscripten
  comp_target_features(lean PUBLIC cpp14_lang/sized_deallocation)
endif()
configure_file("${LEAN_SOURCE_DIR}/compatibility.h.in" "${LEAN_BINARY_DIR}/compatibility.h")

# The DLL (shared library) is not being generated correctly when we use cross-compilation (i.e., generate the Windows DLL using Linux).
# For some strange reason, it contains a copy of pthread_equal.
if (NOT("${CROSS_COMPILE}" MATCHES "ON"))
  add_subdirectory(tests/shared)
endif()
add_subdirectory(tests/util/lp)

# Include style check
if (NOT(${CMAKE_SYSTEM_NAME} MATCHES "Windows") AND PYTHONINTERP_FOUND)
include(StyleCheck)
file(GLOB_RECURSE LEAN_SOURCES
  "${LEAN_SOURCE_DIR}"
  "${LEAN_SOURCE_DIR}/[A-Za-z]*.cpp"
  "${LEAN_SOURCE_DIR}/[A-Za-z]*.h")
add_style_check_target(style "${LEAN_SOURCES}")
add_test(NAME style_check COMMAND "${PYTHON_EXECUTABLE}" "${LEAN_SOURCE_DIR}/cmake/Modules/cpplint.py" ${LEAN_SOURCES})
endif()

add_custom_target(
    standard_lib ALL
    COMMAND "${LEAN_SOURCE_DIR}/../bin/lean" --make ${LEAN_EXTRA_MAKE_OPTS}
    DEPENDS "${CMAKE_BINARY_DIR}/shell/lean"
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../library"
    )

add_custom_target(clean-std-lib
  WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../library"
  COMMAND "${CMAKE_COMMAND}" -P "${CMAKE_MODULE_PATH}/CleanOlean.cmake"
  )

add_custom_target(clean-olean
  DEPENDS clean-std-lib)

if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  install(FILES "${CMAKE_SOURCE_DIR}/../bin/leanemacs.bat" "${CMAKE_SOURCE_DIR}/../bin/leanemacs.bat"
    DESTINATION bin
    PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)
else()
  install(FILES "${CMAKE_SOURCE_DIR}/../bin/leanemacs" "${CMAKE_SOURCE_DIR}/../bin/leanemacs"
    DESTINATION bin
    PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)
endif()

install(DIRECTORY "${CMAKE_SOURCE_DIR}/../library" DESTINATION "${LIBRARY_DIR}"
        FILES_MATCHING
        PATTERN "*.lean"
        PATTERN "*.olean"
        PATTERN ".project"
        PATTERN "*.md")

install(DIRECTORY "${CMAKE_SOURCE_DIR}/" DESTINATION "${LEAN_EXT_INCLUDE_DIR}"
        FILES_MATCHING
        PATTERN "*.h")

install(FILES "${CMAKE_SOURCE_DIR}/../src/emacs/lean.pgm"
        DESTINATION "${EMACS_LISP_DIR}")

if("${INCLUDE_MSYS2_DLLS}" MATCHES "ON")
  # TODO(Leo): do not use hardlinks to required DLLs.
  # For example, we can try to use ldd to retrieve the list of required DLLs.
  set(MINGW_LOCAL_DIR C:/msys64/mingw64/bin)
  set(RUNTIME_LIBRARIES
         ${MINGW_LOCAL_DIR}/libgmp-10.dll
         ${MINGW_LOCAL_DIR}/libwinpthread-1.dll
         ${MINGW_LOCAL_DIR}/libgcc_s_seh-1.dll
         ${MINGW_LOCAL_DIR}/libstdc++-6.dll
         ${MINGW_LOCAL_DIR}/ninja.exe)
  install(PROGRAMS ${RUNTIME_LIBRARIES} DESTINATION bin)
endif()

# CPack
set(CPACK_PACKAGE_NAME lean)
set(CPACK_PACKAGE_CONTACT "Leonardo de Moura <leodemoura@microsoft.com>")
string(TOLOWER ${CMAKE_SYSTEM_NAME} LOWER_SYSTEM_NAME)
string(TIMESTAMP COMPILE_DATETIME "%Y%m%d%H%M%S")
set(CPACK_PACKAGE_VERSION "${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}.${LEAN_VERSION_PATCH}.${COMPILE_DATETIME}")
if(NOT (${GIT_SHA1} MATCHES "GITDIR-NOTFOUND"))
  set(CPACK_PACKAGE_VERSION "${CPACK_PACKAGE_VERSION}.git${GIT_SHA1}")
endif()
set(CPACK_PACKAGE_FILE_NAME "lean-${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}.${LEAN_VERSION_PATCH}-${LOWER_SYSTEM_NAME}")
if(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  SET(CPACK_GENERATOR TGZ)
else()
  SET(CPACK_GENERATOR ZIP)
endif()
# CPack -- Debian
if(STATIC)
  SET(CPACK_DEBIAN_PACKAGE_DEPENDS "")
else()
  SET(CPACK_DEBIAN_PACKAGE_DEPENDS "libstdc++-4.8-dev,libgmp-dev,libmpfr-dev")
endif()
SET(CPACK_DEBIAN_PACKAGE_DESCRIPTION "Lean Theorem Prover")
SET(CPACK_DEBIAN_PACKAGE_SECTION "devel")
include(CPack)

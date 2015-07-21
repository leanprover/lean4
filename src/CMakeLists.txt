cmake_minimum_required(VERSION 2.8.7)
project(LEAN CXX)
set(LEAN_VERSION_MAJOR 0)
set(LEAN_VERSION_MINOR 2)
set(LEAN_VERSION_PATCH 0)

if (NOT CMAKE_BUILD_TYPE)
  message(STATUS "No build type selected, default to Release")
  set(CMAKE_BUILD_TYPE "Release")
endif()

set(CMAKE_COLOR_MAKEFILE ON)
enable_testing()

option(TRACK_MEMORY_USAGE "TRACK_MEMORY_USAGE" ON)
option(MULTI_THREAD       "MULTI_THREAD"       ON)
option(BOOST              "BOOST"              OFF)
option(STATIC             "STATIC"             OFF)
option(SPLIT_STACK        "SPLIT_STACK"        OFF)
option(READLINE           "READLINE"           OFF)
option(CACHE_EXPRS        "CACHE_EXPRS"        ON)
option(TCMALLOC           "TCMALLOC"           ON)
option(JEMALLOC           "JEMALLOC"           OFF)
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
# When ON we add lean binary dependency to standard and HOTT libraries
option(LEAN_BIN_DEP       "LEAN_BIN_DEP"      ON)
# When ON we include githash in the version string
option(USE_GITHASH        "GIT_HASH"          ON)
# Directory that include lean emacs mode dependecies
set(EMACS_DEPENDENCIES "${CMAKE_SOURCE_DIR}/emacs/dependencies")

message(STATUS "Emacs dependecies directory " ${EMACS_DEPENDENCIES})

# emacs site-lisp dir
set(EMACS_LISP_DIR        "share/emacs/site-lisp/lean" CACHE STRING "emacs site-lisp dir")
# library dir
set(LIBRARY_DIR           "lib/lean"                   CACHE STRING "library dir")

message(STATUS "Lean emacs-mode will be installed at "
  "${CMAKE_INSTALL_PREFIX}/${EMACS_LISP_DIR}")
message(STATUS "Lean library will be installed at "
  "${CMAKE_INSTALL_PREFIX}/${LIBRARY_DIR}")

# Added for CTest
include(CTest)
configure_file("${LEAN_SOURCE_DIR}/CTestCustom.cmake.in"
  "${LEAN_BINARY_DIR}/CTestCustom.cmake" @ONLY)

set(LEAN_EXTRA_LINKER_FLAGS "")
set(LEAN_EXTRA_CXX_FLAGS "")

# Windows does not support ulimit -s unlimited. So, we reserve a lot of stack space: 100Mb
if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  message(STATUS "Windows detected")
  set(LEAN_WIN_STACK_SIZE "104857600")
  set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -Wl,--stack,${LEAN_WIN_STACK_SIZE}")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_WINDOWS -D LEAN_WIN_STACK_SIZE=${LEAN_WIN_STACK_SIZE}")
endif()

if("${CYGWIN}" EQUAL "1")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_CYGWIN")
endif()

if(NOT MULTI_THREAD)
  message(STATUS "Disabled multi-thread support, it will not be safe to run multiple threads in parallel")
else()
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_MULTI_THREAD")
endif()

if(CACHE_EXPRS)
  message(STATUS "Lean expression caching enabled (aka partial hashconsing)")
  set(LEAN_EXTRA_CXX_FLAGS "${LEAN_EXTRA_CXX_FLAGS} -D LEAN_CACHE_EXPRS")
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

if("${CMAKE_C_COMPILER}" MATCHES "emcc")
  set(EMSCRIPTEN ON)
  set(CROSS_COMPILE ON)
  set(IGNORE_SORRY ON)
endif()

# Set Module Path
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules")

# Initialize CXXFLAGS.
set(CMAKE_CXX_FLAGS                "-Wall -Wextra -std=c++11 ${LEAN_EXTRA_CXX_FLAGS} -DLEAN_BUILD_TYPE=\"${CMAKE_BUILD_TYPE}\"")
set(CMAKE_CXX_FLAGS_DEBUG          "-g -DLEAN_DEBUG -DLEAN_TRACE")
set(CMAKE_CXX_FLAGS_MINSIZEREL     "-Os -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELEASE        "-O3 -DNDEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")
set(CMAKE_CXX_FLAGS_GPROF          "-O2 -g -pg")
set(CMAKE_CXX_FLAGS_EMSCRIPTEN     "-Oz -s DISABLE_EXCEPTION_CATCHING=0 -D LEAN_EMSCRIPTEN -Wno-warn-absolute-paths --bind")

# OSX .dmg generation (this is working in progress)
set(CPACK_DMG_BACKGROUND_IMAGE "${LEAN_SOURCE_DIR}/../images/lean.png")
set(CPACK_DMG_VOLUME_NAME "Lean-${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}")
set(CPACK_BUNDLE_NAME "Lean-${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}")
set(CPACK_BUNDLE_STARTUP_COMMAND "bin/leanemacs")
set(CPACK_PACKAGE_FILE_NAME "Lean-${LEAN_VERSION_MAJOR}.${LEAN_VERSION_MINOR}")
set(CPACK_PACKAGE_ICON "${LEAN_SOURCE_DIR}/../images/lean.png")
##################

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
  include(CodeCoverage)
  message(STATUS "Enable test-coverage")
  set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -O0 -fprofile-arcs -ftest-coverage --coverage")
  setup_target_for_coverage(cov "${LEAN_SOURCE_DIR}/../script/run_tests.sh" coverage)
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

# BOOST
if (BOOST AND MULTI_THREAD)
  find_package(Boost 1.54 COMPONENTS system thread atomic chrono REQUIRED)
  message(STATUS "Boost library will be used to implement multi-threading support")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D LEAN_USE_BOOST")
  set(EXTRA_LIBS ${EXTRA_LIBS} ${Boost_LIBRARIES})
  if (("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin") AND ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
     # Hide warnings when using Boost and g++ on OSX
     set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-unused-local-typedefs -Wno-deprecated-declarations")
  endif()
endif()

# MPFR
find_package(MPFR 3.1.0 REQUIRED)
include_directories(${MPFR_INCLUDES})
set(EXTRA_LIBS ${EXTRA_LIBS} ${MPFR_LIBRARIES})

# GMP
find_package(GMP 5.0.5 REQUIRED)
include_directories(${GMP_INCLUDE_DIR})
set(EXTRA_LIBS ${EXTRA_LIBS} ${GMP_LIBRARIES})

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

# Check malloc_usable_size
if(NOT "${EMSCRIPTEN}" AND NOT "${TCMALLOC_FOUND}" AND NOT "${JEMALLOC_FOUND}" AND TRACK_MEMORY_USAGE)
  find_package(MallocUsableSize)
  if(MUS_FOUND)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${MALLOC_DIR} -D HAS_MALLOC_USABLE_SIZE")
  else()
    find_package(MallocSize)
    if(MALLOCSIZE_FOUND)
      set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${MALLOC_DIR} -D HAS_MALLOCSIZE")
    else()
      find_package(MSize)
      if(MSIZE_FOUND)
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${MALLOC_DIR} -D HAS_MSIZE")
      endif()
    endif()
  endif()
endif()

# Lua
find_package(Lua REQUIRED)
set(EXTRA_LIBS ${EXTRA_LIBS} ${LUA_LIBRARIES})
if(NOT "${EMSCRIPTEN}" AND ${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  # Lua static library for linux depends on dl.so
  set(EXTRA_LIBS ${EXTRA_LIBS} -ldl)
endif()
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I ${LUA_INCLUDE_DIR}")
if (HAS_LUA_NEWSTATE)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D LEAN_USE_LUA_NEWSTATE")
endif()

IF(${CMAKE_SYSTEM_NAME} MATCHES "Darwin" AND ${LUA_FOUND} AND
    "${LUA_INCLUDE_DIR}" MATCHES "jit")
  # http://luajit.org/install.html
  # If you're building a 64 bit application on OSX which links
  # directly or indirectly against LuaJIT, you need to link your main
  # executable with these flags:
  set(LEAN_EXTRA_LINKER_FLAGS "${LEAN_EXTRA_LINKER_FLAGS} -pagezero_size 10000 -image_base 100000000")
ENDIF()

# Python
find_package(PythonInterp REQUIRED)

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

# linja
configure_file("${LEAN_SOURCE_DIR}/../bin/linja.in" "${LEAN_SOURCE_DIR}/../bin/linja" @ONLY)

include_directories("${LEAN_BINARY_DIR}")
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
add_subdirectory(kernel/inductive)
set(LEAN_LIBS ${LEAN_LIBS} inductive)
add_subdirectory(kernel/quotient)
set(LEAN_LIBS ${LEAN_LIBS} quotient)
add_subdirectory(kernel/hits)
set(LEAN_LIBS ${LEAN_LIBS} hits)
add_subdirectory(library)
set(LEAN_LIBS ${LEAN_LIBS} library)
add_subdirectory(library/simplifier)
set(LEAN_LIBS ${LEAN_LIBS} simplifier)
add_subdirectory(library/tactic)
set(LEAN_LIBS ${LEAN_LIBS} tactic)
add_subdirectory(library/definitional)
set(LEAN_LIBS ${LEAN_LIBS} definitional)
add_subdirectory(library/error_handling)
set(LEAN_LIBS ${LEAN_LIBS} error_handling)
add_subdirectory(frontends/lean)
set(LEAN_LIBS ${LEAN_LIBS} lean_frontend)
add_subdirectory(frontends/lua)
set(LEAN_LIBS ${LEAN_LIBS} leanlua)
add_subdirectory(init)
set(LEAN_LIBS ${LEAN_LIBS} init)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LEAN_EXTRA_LINKER_FLAGS}")
if(MULTI_THREAD AND (NOT ("${CMAKE_SYSTEM_NAME}" MATCHES "Darwin")) AND (NOT BOOST))
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread")
endif()
set(CMAKE_EXE_LINKER_FLAGS_TESTCOV "${CMAKE_EXE_LINKER_FLAGS} -fprofile-arcs -ftest-coverage")
set(ALL_LIBS ${LEAN_LIBS} ${EXTRA_LIBS})
add_subdirectory(shell)
set(LEAN_LIBS ${LEAN_LIBS} shell)
add_subdirectory(emacs)
add_subdirectory(tests/util)
add_subdirectory(tests/util/numerics)
add_subdirectory(tests/util/interval)
add_subdirectory(tests/kernel)
add_subdirectory(tests/library)
add_subdirectory(tests/library/blast)
add_subdirectory(tests/frontends/lean)
add_subdirectory(tests/shell)

# Include style check
if (NOT(${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
include(StyleCheck)
file(GLOB_RECURSE LEAN_SOURCES
  "${LEAN_SOURCE_DIR}"
  "${LEAN_SOURCE_DIR}/[A-Za-z]*.cpp"
  "${LEAN_SOURCE_DIR}/[A-Za-z]*.h")
add_style_check_target(style "${LEAN_SOURCES}")
add_test(NAME style_check COMMAND "${PYTHON_EXECUTABLE}" "${LEAN_SOURCE_DIR}/cmake/Modules/cpplint.py" ${LEAN_SOURCES})
endif()

# Set PROCESSOR_COUNT
if(NOT DEFINED PROCESSOR_COUNT)
  # Unknown:
  set(PROCESSOR_COUNT 1)

  # Linux:
  set(cpuinfo_file "/proc/cpuinfo")
  if(EXISTS "${cpuinfo_file}")
    file(STRINGS "${cpuinfo_file}" procs REGEX "^processor.: [0-9]+$")
    list(LENGTH procs PROCESSOR_COUNT)
  endif()

  # Mac:
  if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
     execute_process(COMMAND "sysctl" "hw.ncpu" OUTPUT_VARIABLE info)
     string(REGEX REPLACE "^hw.ncpu: ([0-9]+).*$" "\\1" PROCESSOR_COUNT "${info}")
  endif()

  # Windows:
  if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
    set(PROCESSOR_COUNT "$ENV{NUMBER_OF_PROCESSORS}")
  endif()
endif()

if("${CROSS_COMPILE}" MATCHES "ON" OR "${CMAKE_C_COMPILER}" MATCHES "emcc")
  message(STATUS "Lean standard library will not be compiled when using cross-compilation.")
else()
  add_custom_target(
    standard_lib ALL
    COMMAND "${PYTHON_EXECUTABLE}" "${LEAN_SOURCE_DIR}/../bin/linja" all tags
    DEPENDS "${CMAKE_BINARY_DIR}/shell/lean"
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../library"
    )
  add_custom_target(
    hott_lib ALL
    COMMAND "${PYTHON_EXECUTABLE}" "${LEAN_SOURCE_DIR}/../bin/linja" all tags
    DEPENDS "${CMAKE_BINARY_DIR}/shell/lean"
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../hott"
    )
endif()

add_custom_target(clean-std-lib
  WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../library"
  COMMAND "${CMAKE_COMMAND}" -P "${CMAKE_MODULE_PATH}/CleanOlean.cmake"
  )

add_custom_target(clean-hott-lib
  WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../hott"
  COMMAND "${CMAKE_COMMAND}" -P "${CMAKE_MODULE_PATH}/CleanOlean.cmake"
  )

add_custom_target(clean-olean
  DEPENDS clean-std-lib clean-hott-lib)

install(FILES "${CMAKE_SOURCE_DIR}/../bin/linja" "${CMAKE_SOURCE_DIR}/../bin/leantags"
  DESTINATION bin
  PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE GROUP_READ GROUP_EXECUTE WORLD_READ WORLD_EXECUTE)

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
        FILES_MATCHING PATTERN "*.lean")
install(DIRECTORY "${CMAKE_SOURCE_DIR}/../library" DESTINATION "${LIBRARY_DIR}"
        FILES_MATCHING
        PATTERN "*.lean"
        PATTERN "*.olean"
        PATTERN ".project"
        PATTERN "TAGS")

install(DIRECTORY "${CMAKE_SOURCE_DIR}/../hott" DESTINATION "${LIBRARY_DIR}"
        FILES_MATCHING PATTERN "*.hlean")
install(DIRECTORY "${CMAKE_SOURCE_DIR}/../hott" DESTINATION "${LIBRARY_DIR}"
        FILES_MATCHING
        PATTERN "*.lean"
        PATTERN "*.olean"
        PATTERN ".project"
        PATTERN "TAGS")

install(FILES "${CMAKE_SOURCE_DIR}/../src/emacs/lean.pgm"
        DESTINATION "${EMACS_LISP_DIR}")

if(EXISTS "${EMACS_DEPENDENCIES}")
  install(DIRECTORY "${EMACS_DEPENDENCIES}/" DESTINATION "${EMACS_LISP_DIR}/dependencies"
    FILES_MATCHING
    PATTERN "*.el"
    PATTERN "dir"
    PATTERN "*.info*")
else()
  message(STATUS "Emacs dependencies directory does not exist. Therefore, they will not be included in the binary installation package. The Emacs packages required by Lean Emacs mode can be retrieved from the repository https://github.com/leanprover/emacs-dependencies. The cmake option EMACS_DEPENDENCIES can be used to specify where these files are located.")
endif()

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
  SET(CPACK_DEBIAN_PACKAGE_DEPENDS "python")
else()
  SET(CPACK_DEBIAN_PACKAGE_DEPENDS "libstdc++-4.8-dev,libgmp-dev,libmpfr-dev,liblua5.2-dev,python")
endif()
SET(CPACK_DEBIAN_PACKAGE_DESCRIPTION "Lean Theorem Prover")
SET(CPACK_DEBIAN_PACKAGE_SECTION "devel")
include(CPack)

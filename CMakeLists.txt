cmake_minimum_required(VERSION 3.21)
include(ExternalProject)
include(FetchContent)

if(NOT CMAKE_GENERATOR MATCHES "Makefiles")
  message(FATAL_ERROR "Only makefile generators are supported")
endif()

option(USE_MIMALLOC "use mimalloc" ON)

# store all variables passed on the command line into CL_ARGS so we can pass them to the stage builds
# MUST be done before call to 'project'
# Use standard release build (discarding LEAN_EXTRA_CXX_FLAGS etc.) for stage0 by default since it is assumed to be "good", but still pass through CMake platform arguments (compiler, toolchain file, ..).
# Use `STAGE0_` prefix to pass variables to stage0 explicitly.
get_cmake_property(vars CACHE_VARIABLES)
foreach(var ${vars})
  get_property(currentType CACHE "${var}" PROPERTY TYPE)
  if(var MATCHES "STAGE0_(.*)")
    list(APPEND STAGE0_ARGS "-D${CMAKE_MATCH_1}=${${var}}")
  elseif(var MATCHES "STAGE1_(.*)")
    list(APPEND STAGE1_ARGS "-D${CMAKE_MATCH_1}=${${var}}")
  # NOTE: does not catch `-DFOO:BAR=` typed uses
  elseif(currentType STREQUAL "UNINITIALIZED")
    list(APPEND CL_ARGS "-D${var}=${${var}}")
    if(var MATCHES "USE_GMP|CHECK_OLEAN_VERSION|LEAN_VERSION_.*|LEAN_SPECIAL_VERSION_DESC")
      # must forward options that generate incompatible .olean format
      list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
    elseif(var MATCHES "LLVM*|PKG_CONFIG|USE_LAKE|USE_MIMALLOC|FORCE_GMP")
      list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
    endif()
  elseif(var MATCHES "USE_MIMALLOC")
    list(APPEND CL_ARGS "-D${var}=${${var}}")
    list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
  elseif((var MATCHES "CMAKE_.*") AND NOT (var MATCHES "CMAKE_BUILD_TYPE") AND NOT (var MATCHES "CMAKE_HOME_DIRECTORY"))
    list(APPEND PLATFORM_ARGS "-D${var}=${${var}}")
  endif()
endforeach()

project(LEAN CXX C)

if(NOT (DEFINED STAGE0_CMAKE_EXECUTABLE_SUFFIX))
  set(STAGE0_CMAKE_EXECUTABLE_SUFFIX "${CMAKE_EXECUTABLE_SUFFIX}")
endif()

# Don't do anything with cadical/leantar on wasm
if(NOT CMAKE_SYSTEM_NAME MATCHES "Emscripten")
  find_program(CADICAL cadical)
  # `libcadical.a` is linked into the Lean libraries, so it has to be built with matching flags
  # (position-independent, hidden visibility). Packagers can point these at their own build to
  # avoid the source fetch below, but then have to provide all three.
  set(CADICAL_LIB "" CACHE FILEPATH "Path to a static libcadical to link into the Lean libraries")
  set(CADICAL_INCLUDE_DIR "" CACHE PATH "Directory containing cadical.hpp")
  if(NOT (CADICAL AND CADICAL_LIB AND CADICAL_INCLUDE_DIR))
    # cadical's objects end up in `libcadical.a`, which is linked into the Lean libraries, so the two
    # have to agree on the compiler and C++ runtime.
    set(CADICAL_CXX ${CMAKE_CXX_COMPILER})
    # Use same platform flags as for Lean executables, in particular from `prepare-llvm-linux.sh`,
    # but not Lean-specific `LEAN_EXTRA_CXX_FLAGS` such as fsanitize. `prepare-llvm-mingw.sh` cannot
    # put its sysroot into `CMAKE_CXX_FLAGS` because stage0 uses a different compiler there, so it
    # passes the flags cadical needs separately.
    set(CADICAL_EXTRA_CXX_FLAGS "" CACHE STRING "Additional flags used to compile cadical")
    set(CADICAL_CXXFLAGS "${CMAKE_CXX_FLAGS} ${CADICAL_EXTRA_CXX_FLAGS}")
    string(REPLACE "ROOT" "${CMAKE_BINARY_DIR}/stage1" CADICAL_INTERNAL_LINKER_FLAGS "${LEANC_INTERNAL_LINKER_FLAGS}")
    set(CADICAL_LDFLAGS "${CADICAL_INTERNAL_LINKER_FLAGS}")
    if(CMAKE_SYSTEM_NAME MATCHES "Linux")
      string(APPEND CADICAL_LDFLAGS " -Wl,-rpath=\\$$ORIGIN/../lib")
    elseif(CMAKE_SYSTEM_NAME MATCHES "Darwin")
      string(APPEND CADICAL_LDFLAGS " -Wl,-rpath,@executable_path/../lib")
    endif()
    find_program(CCACHE ccache)
    if(CCACHE)
      set(CADICAL_CXX "${CCACHE} ${CADICAL_CXX}")
    endif()
    # missing stdio locking API on Windows
    if(CMAKE_SYSTEM_NAME MATCHES "Windows")
      string(APPEND CADICAL_CXXFLAGS " -DNUNLOCKED")
    endif()
    string(APPEND CADICAL_CXXFLAGS " -DNCLOSEFROM")
    if(CMAKE_SYSTEM_NAME MATCHES "Linux")
      string(APPEND CADICAL_CXXFLAGS " -fPIC")
    endif()
    if(NOT CMAKE_SYSTEM_NAME MATCHES "Windows")
      # do not re-export cadical from `libleanshared`
      string(APPEND CADICAL_CXXFLAGS " -fvisibility=hidden")
    endif()
    ExternalProject_Add(
      cadical
      PREFIX cadical
      GIT_REPOSITORY https://github.com/arminbiere/cadical
      GIT_TAG rel-2.1.2
      CONFIGURE_COMMAND ""
      BUILD_COMMAND
        $(MAKE) -f ${CMAKE_SOURCE_DIR}/src/cadical.mk CMAKE_EXECUTABLE_SUFFIX=${CMAKE_EXECUTABLE_SUFFIX}
        CXX=${CADICAL_CXX} CXXFLAGS=${CADICAL_CXXFLAGS} LDFLAGS=${CADICAL_LDFLAGS} AR=${CMAKE_AR}
      BUILD_IN_SOURCE ON
      INSTALL_COMMAND ""
      BUILD_BYPRODUCTS
        ${CMAKE_BINARY_DIR}/cadical/cadical${CMAKE_EXECUTABLE_SUFFIX} ${CMAKE_BINARY_DIR}/cadical/libcadical.a
    )
    if(NOT CADICAL)
      set(CADICAL ${CMAKE_BINARY_DIR}/cadical/cadical${CMAKE_EXECUTABLE_SUFFIX})
    endif()
    if(NOT CADICAL_LIB)
      set(CADICAL_LIB ${CMAKE_BINARY_DIR}/cadical/libcadical.a)
    endif()
    if(NOT CADICAL_INCLUDE_DIR)
      set(CADICAL_INCLUDE_DIR ${CMAKE_BINARY_DIR}/cadical/src/cadical/src)
    endif()
    list(APPEND EXTRA_DEPENDS cadical)
  endif()
  find_program(LEANTAR leantar)
  if(NOT LEANTAR)
    set(LEANTAR_VERSION v0.1.20)
    if(CMAKE_SYSTEM_NAME MATCHES "Windows")
      set(LEANTAR_ARCHIVE_SUFFIX .zip)
      set(LEANTAR_TARGET x86_64-pc-windows-msvc)
    else()
      set(LEANTAR_ARCHIVE_SUFFIX .tar.gz)
      if(CMAKE_SYSTEM_PROCESSOR MATCHES "arm64|aarch64")
        set(LEANTAR_TARGET_ARCH aarch64)
      else()
        set(LEANTAR_TARGET_ARCH x86_64)
      endif()
      if(CMAKE_SYSTEM_NAME MATCHES "Darwin")
        set(LEANTAR_TARGET_OS apple-darwin)
      else()
        set(LEANTAR_TARGET_OS unknown-linux-musl)
      endif()
      set(LEANTAR_TARGET ${LEANTAR_TARGET_ARCH}-${LEANTAR_TARGET_OS})
    endif()
    set(
      LEANTAR
      ${CMAKE_BINARY_DIR}/leantar/leantar-${LEANTAR_VERSION}-${LEANTAR_TARGET}/leantar${CMAKE_EXECUTABLE_SUFFIX}
    )
    if(NOT EXISTS "${LEANTAR}")
      file(
        DOWNLOAD
          https://github.com/digama0/leangz/releases/download/${LEANTAR_VERSION}/leantar-${LEANTAR_VERSION}-${LEANTAR_TARGET}${LEANTAR_ARCHIVE_SUFFIX}
        ${CMAKE_BINARY_DIR}/leantar${LEANTAR_ARCHIVE_SUFFIX}
        STATUS LEANTAR_DOWNLOAD_STATUS
      )
      list(GET LEANTAR_DOWNLOAD_STATUS 0 LEANTAR_DOWNLOAD_CODE)
      if(NOT LEANTAR_DOWNLOAD_CODE EQUAL 0)
        list(GET LEANTAR_DOWNLOAD_STATUS 1 LEANTAR_DOWNLOAD_ERROR)
        message(FATAL_ERROR "Failed to download leantar: ${LEANTAR_DOWNLOAD_ERROR}")
      endif()
      file(
        ARCHIVE_EXTRACT
        INPUT ${CMAKE_BINARY_DIR}/leantar${LEANTAR_ARCHIVE_SUFFIX}
        DESTINATION ${CMAKE_BINARY_DIR}/leantar
      )
    endif()
  endif()
  set(
    CADICAL_ARGS
    -DCADICAL=${CADICAL} -DCADICAL_LIB=${CADICAL_LIB} -DCADICAL_INCLUDE_DIR=${CADICAL_INCLUDE_DIR}
  )
  list(APPEND STAGE0_ARGS ${CADICAL_ARGS} -DLEANTAR=${LEANTAR})
  list(APPEND CL_ARGS ${CADICAL_ARGS} -DLEANTAR=${LEANTAR})
endif()

if(USE_MIMALLOC)
  FetchContent_Declare(
    mimalloc
    GIT_REPOSITORY https://github.com/microsoft/mimalloc
    GIT_BRANCH dev3
    GIT_TAG v3.4.5
    # Unnecessarily deep directory structure, but it saves us from a complicated
    # stage0 update for now. If we ever update the other dependencies like
    # cadical, it might be worth reorganizing the directory structure.
    SOURCE_DIR
    "${CMAKE_BINARY_DIR}/mimalloc/src/mimalloc"
    EXCLUDE_FROM_ALL
  )
  FetchContent_MakeAvailable(mimalloc)
endif()

if(NOT STAGE1_PREV_STAGE)
  ExternalProject_Add(
    stage0
    SOURCE_DIR "${LEAN_SOURCE_DIR}/stage0"
    SOURCE_SUBDIR src
    BINARY_DIR stage0
    # do not rebuild stage0 when git hash changes; it's not from this commit anyway
    # (however, CI will override this as we need to embed the githash into the stage 1 library built
    # by stage 0)
    CMAKE_ARGS -DSTAGE=0 -DUSE_GITHASH=OFF ${PLATFORM_ARGS} ${STAGE0_ARGS}
    BUILD_ALWAYS
      ON # cmake doesn't auto-detect changes without a download method
    INSTALL_COMMAND
      "" # skip install
    DEPENDS ${EXTRA_DEPENDS}
  )
  list(APPEND EXTRA_DEPENDS stage0)
endif()
ExternalProject_Add(
  stage1
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage1
  CMAKE_ARGS
    -DSTAGE=1 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage0
    -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX=${STAGE0_CMAKE_EXECUTABLE_SUFFIX} ${CL_ARGS} ${STAGE1_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS ${EXTRA_DEPENDS}
  STEP_TARGETS configure
)
ExternalProject_Add(
  stage2
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage2
  CMAKE_ARGS
    -DSTAGE=2 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage1 -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX=${CMAKE_EXECUTABLE_SUFFIX}
    ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage1
  EXCLUDE_FROM_ALL ON
  STEP_TARGETS configure
)
ExternalProject_Add(
  stage3
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage3
  CMAKE_ARGS
    -DSTAGE=3 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage2 -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX=${CMAKE_EXECUTABLE_SUFFIX}
    ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage2
  EXCLUDE_FROM_ALL ON
  STEP_TARGETS configure
)

# targets forwarded to appropriate stages

add_custom_target(update-stage0 COMMAND $(MAKE) -C stage1 update-stage0 DEPENDS stage1)

add_custom_target(update-stage0-commit COMMAND $(MAKE) -C stage1 update-stage0-commit DEPENDS stage1)

add_custom_target(test COMMAND $(MAKE) -C stage1 test DEPENDS stage1)

add_custom_target(
  bench
  COMMAND $(MAKE) -C stage2
  COMMAND $(MAKE) -C stage2 -j1 bench
  DEPENDS stage2
)
add_custom_target(
  bench-part1
  COMMAND $(MAKE) -C stage2
  COMMAND $(MAKE) -C stage2 -j1 bench-part1
  DEPENDS stage2
)
add_custom_target(
  bench-part2
  COMMAND $(MAKE) -C stage2
  COMMAND $(MAKE) -C stage2 -j1 bench-part2
  DEPENDS stage2
)

add_custom_target(clean-stdlib COMMAND $(MAKE) -C stage1 clean-stdlib DEPENDS stage1-configure)

add_custom_target(cache-get COMMAND $(MAKE) -C stage1 cache-get DEPENDS stage1-configure)

install(CODE "execute_process(COMMAND make -C stage1 install)")

add_custom_target(check-stage3 COMMAND diff "stage2/bin/lean" "stage3/bin/lean" DEPENDS stage3)

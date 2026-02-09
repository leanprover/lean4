cmake_minimum_required(VERSION 3.21)

option(USE_MIMALLOC "use mimalloc" ON)

# store all variables passed on the command line into CL_ARGS so we can pass them to the stage builds
# https://stackoverflow.com/a/48555098/161659
# MUST be done before call to 'project'
# Use standard release build (discarding LEAN_EXTRA_CXX_FLAGS etc.) for stage0 by default since it is assumed to be "good", but still pass through CMake platform arguments (compiler, toolchain file, ..).
# Use `STAGE0_` prefix to pass variables to stage0 explicitly.
get_cmake_property(vars CACHE_VARIABLES)
foreach(var ${vars})
  get_property(currentHelpString CACHE "${var}" PROPERTY HELPSTRING)
  if(var MATCHES "STAGE0_(.*)")
    list(APPEND STAGE0_ARGS "-D${CMAKE_MATCH_1}=${${var}}")
  elseif(var MATCHES "STAGE1_(.*)")
    list(APPEND STAGE1_ARGS "-D${CMAKE_MATCH_1}=${${var}}")
  elseif(currentHelpString MATCHES "No help, variable specified on the command line." OR currentHelpString STREQUAL "")
    list(APPEND CL_ARGS "-D${var}=${${var}}")
    if(var MATCHES "USE_GMP|CHECK_OLEAN_VERSION|LEAN_VERSION_.*|LEAN_SPECIAL_VERSION_DESC")
      # must forward options that generate incompatible .olean format
      list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
    elseif(var MATCHES "LLVM*|PKG_CONFIG|USE_LAKE|USE_MIMALLOC")
      list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
    endif()
  elseif(var MATCHES "USE_MIMALLOC")
    list(APPEND CL_ARGS "-D${var}=${${var}}")
    list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
  elseif((var MATCHES "CMAKE_.*") AND NOT (var MATCHES "CMAKE_BUILD_TYPE") AND NOT (var MATCHES "CMAKE_HOME_DIRECTORY"))
    list(APPEND PLATFORM_ARGS "-D${var}=${${var}}")
  endif()
endforeach()

include(ExternalProject)
project(LEAN CXX C)

if(NOT (DEFINED STAGE0_CMAKE_EXECUTABLE_SUFFIX))
  set(STAGE0_CMAKE_EXECUTABLE_SUFFIX "${CMAKE_EXECUTABLE_SUFFIX}")
endif()

# Don't do anything with cadical on wasm
if(NOT CMAKE_SYSTEM_NAME MATCHES "Emscripten")
  find_program(CADICAL cadical)
  if(NOT CADICAL)
    set(CADICAL_CXX c++)
    if(CADICAL_USE_CUSTOM_CXX)
      set(CADICAL_CXX ${CMAKE_CXX_COMPILER})
      # Use same platform flags as for Lean executables, in particular from `prepare-llvm-linux.sh`,
      # but not Lean-specific `LEAN_EXTRA_CXX_FLAGS` such as fsanitize.
      set(CADICAL_CXXFLAGS "${CMAKE_CXX_FLAGS}")
      set(CADICAL_LDFLAGS "-Wl,-rpath=\\$$ORIGIN/../lib")
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
    ExternalProject_Add(
      cadical
      PREFIX cadical
      GIT_REPOSITORY https://github.com/arminbiere/cadical
      GIT_TAG rel-2.1.2
      CONFIGURE_COMMAND ""
      BUILD_COMMAND
        $(MAKE) -f ${CMAKE_SOURCE_DIR}/src/cadical.mk CMAKE_EXECUTABLE_SUFFIX=${CMAKE_EXECUTABLE_SUFFIX}
        CXX=${CADICAL_CXX} CXXFLAGS=${CADICAL_CXXFLAGS} LDFLAGS=${CADICAL_LDFLAGS}
      BUILD_IN_SOURCE ON
      INSTALL_COMMAND ""
    )
    set(CADICAL ${CMAKE_BINARY_DIR}/cadical/cadical${CMAKE_EXECUTABLE_SUFFIX})
    list(APPEND EXTRA_DEPENDS cadical)
  endif()
  list(APPEND CL_ARGS -DCADICAL=${CADICAL})
endif()

if(USE_MIMALLOC)
  ExternalProject_Add(
    mimalloc
    PREFIX mimalloc
    GIT_REPOSITORY https://github.com/microsoft/mimalloc
    GIT_TAG v2.2.3
    # just download, we compile it as part of each stage as it is small
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ""
  )
  list(APPEND EXTRA_DEPENDS mimalloc)
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
)

# targets forwarded to appropriate stages

add_custom_target(update-stage0 COMMAND $(MAKE) -C stage1 update-stage0 DEPENDS stage1)

add_custom_target(update-stage0-commit COMMAND $(MAKE) -C stage1 update-stage0-commit DEPENDS stage1)

add_custom_target(test COMMAND $(MAKE) -C stage1 test DEPENDS stage1)

add_custom_target(clean-stdlib COMMAND $(MAKE) -C stage1 clean-stdlib DEPENDS stage1)

install(CODE "execute_process(COMMAND make -C stage1 install)")

add_custom_target(check-stage3 COMMAND diff "stage2/bin/lean" "stage3/bin/lean" DEPENDS stage3)

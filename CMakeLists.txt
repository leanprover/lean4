cmake_minimum_required(VERSION 3.11)
# store all variables passed on the command line into CL_ARGS so we can pass them to the stage builds
# https://stackoverflow.com/a/48555098/161659
# MUST be done before call to 'project'
# Use standard release build (discarding LEAN_CXX_EXTRA_FLAGS etc.) for stage0 by default since it is assumed to be "good", but still pass through CMake platform arguments (compiler, toolchain file, ..).
# Use `STAGE0_` prefix to pass variables to stage0 explicitly.
get_cmake_property(vars CACHE_VARIABLES)
foreach(var ${vars})
  get_property(currentHelpString CACHE "${var}" PROPERTY HELPSTRING)
  if("${var}" MATCHES "STAGE0_(.*)")
    list(APPEND STAGE0_ARGS "-D${CMAKE_MATCH_1}=${${var}}")
  elseif("${currentHelpString}" MATCHES "No help, variable specified on the command line." OR "${currentHelpString}" STREQUAL "")
    list(APPEND CL_ARGS "-D${var}=${${var}}")
    if("${var}" MATCHES "USE_GMP|CHECK_OLEAN_VERSION")
      # must forward options that generate incompatible .olean format
      list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
    endif()
    if("${var}" MATCHES "LLVM*")
      list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
    endif()
    if("${var}" MATCHES "PKG_CONFIG*")
      list(APPEND STAGE0_ARGS "-D${var}=${${var}}")
    endif()
  elseif(("${var}" MATCHES "CMAKE_.*") AND NOT ("${var}" MATCHES "CMAKE_BUILD_TYPE") AND NOT ("${var}" MATCHES "CMAKE_HOME_DIRECTORY"))
    list(APPEND PLATFORM_ARGS "-D${var}=${${var}}")
  endif()
endforeach()

include(ExternalProject)
project(LEAN CXX C)

if(NOT (DEFINED STAGE0_CMAKE_EXECUTABLE_SUFFIX))
    set(STAGE0_CMAKE_EXECUTABLE_SUFFIX "${CMAKE_EXECUTABLE_SUFFIX}")
endif()

# Don't do anything with cadical on wasm
if (NOT ${CMAKE_SYSTEM_NAME} MATCHES "Emscripten")
  # On CI Linux, we source cadical from Nix instead; see flake.nix
  find_program(CADICAL cadical)
  if(NOT CADICAL)
    set(CADICAL_CXX c++)
    find_program(CCACHE ccache)
    if(CCACHE)
      set(CADICAL_CXX "${CCACHE} ${CADICAL_CXX}")
    endif()
    # missing stdio locking API on Windows
    if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
      string(APPEND CADICAL_CXXFLAGS " -DNUNLOCKED")
    endif()
    string(APPEND CADICAL_CXXFLAGS " -DNCLOSEFROM")
    ExternalProject_add(cadical
      PREFIX cadical
      GIT_REPOSITORY https://github.com/arminbiere/cadical
      GIT_TAG rel-2.1.2
      CONFIGURE_COMMAND ""
      # https://github.com/arminbiere/cadical/blob/master/BUILD.md#manual-build
      BUILD_COMMAND $(MAKE) -f ${CMAKE_SOURCE_DIR}/src/cadical.mk CMAKE_EXECUTABLE_SUFFIX=${CMAKE_EXECUTABLE_SUFFIX} CXX=${CADICAL_CXX} CXXFLAGS=${CADICAL_CXXFLAGS}
      BUILD_IN_SOURCE ON
      INSTALL_COMMAND "")
    set(CADICAL ${CMAKE_BINARY_DIR}/cadical/cadical${CMAKE_EXECUTABLE_SUFFIX} CACHE FILEPATH "path to cadical binary" FORCE)
    set(EXTRA_DEPENDS "cadical")
  endif()
  list(APPEND CL_ARGS -DCADICAL=${CADICAL})
endif()

ExternalProject_add(stage0
  SOURCE_DIR "${LEAN_SOURCE_DIR}/stage0"
  SOURCE_SUBDIR src
  BINARY_DIR stage0
  # do not rebuild stage0 when git hash changes; it's not from this commit anyway
  # (however, `CHECK_OLEAN_VERSION=ON` in CI will override this as we need to
  # embed the githash into the stage 1 library built by stage 0)
  CMAKE_ARGS -DSTAGE=0 -DUSE_GITHASH=OFF ${PLATFORM_ARGS} ${STAGE0_ARGS}
  BUILD_ALWAYS ON  # cmake doesn't auto-detect changes without a download method
  INSTALL_COMMAND ""  # skip install
  DEPENDS ${EXTRA_DEPENDS}
)
ExternalProject_add(stage1
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage1
  CMAKE_ARGS -DSTAGE=1 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage0 -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX=${STAGE0_CMAKE_EXECUTABLE_SUFFIX} ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage0
)
ExternalProject_add(stage2
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage2
  CMAKE_ARGS -DSTAGE=2 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage1 -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX=${CMAKE_EXECUTABLE_SUFFIX} ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage1
  EXCLUDE_FROM_ALL ON
)
ExternalProject_add(stage3
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage3
  CMAKE_ARGS -DSTAGE=3 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage2 -DPREV_STAGE_CMAKE_EXECUTABLE_SUFFIX=${CMAKE_EXECUTABLE_SUFFIX} ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage2
  EXCLUDE_FROM_ALL ON
)

# targets forwarded to appropriate stages

add_custom_target(update-stage0
  COMMAND $(MAKE) -C stage1 update-stage0
  DEPENDS stage1)

add_custom_target(update-stage0-commit
  COMMAND $(MAKE) -C stage1 update-stage0-commit
  DEPENDS stage1)

add_custom_target(test
  COMMAND $(MAKE) -C stage1 test
  DEPENDS stage1)

install(CODE "execute_process(COMMAND make -C stage1 install)")

add_custom_target(check-stage3
  COMMAND diff "stage2/bin/lean" "stage3/bin/lean"
  DEPENDS stage3)

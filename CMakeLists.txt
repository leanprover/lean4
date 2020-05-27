cmake_minimum_required(VERSION 3.11)
# store all variables passed on the command line into CL_ARGS so we can pass them to the stage builds
# https://stackoverflow.com/a/48555098/161659
# MUST be done before call to 'project'
get_cmake_property(vars CACHE_VARIABLES)
foreach(var ${vars})
  get_property(currentHelpString CACHE "${var}" PROPERTY HELPSTRING)
  if("${currentHelpString}" MATCHES "No help, variable specified on the command line." OR "${currentHelpString}" STREQUAL "")
    list(APPEND CL_ARGS "-D${var}=${${var}}")
  endif()
endforeach()

include(ExternalProject)
project(LEAN CXX C)
# use the same library sources everywhere; this only important for stage 0 since the compiler source for it come from stage0/src
list(APPEND CL_ARGS "-DLIB_SOURCE_DIR=${LEAN_SOURCE_DIR}/src")

ExternalProject_add(stage0
  SOURCE_DIR "${LEAN_SOURCE_DIR}/stage0"
  SOURCE_SUBDIR src
  BINARY_DIR stage0
  # do not rebuild stage0 when git hash changes; it's not from this commit anyway
  CMAKE_ARGS -DSTAGE=0 ${CL_ARGS} -DUSE_GITHASH=OFF
  BUILD_ALWAYS ON  # cmake doesn't auto-detect changes without a download method
  INSTALL_COMMAND ""  # skip install
)
ExternalProject_add(stage0.5
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage0.5
  CMAKE_ARGS -DSTAGE=0.5 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage0 ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage0
)
ExternalProject_add(stage1
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage1
  # reuse libleancpp.a, which doesn't change
  CMAKE_ARGS -DSTAGE=1 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage0 -DLEANCPP="${CMAKE_BINARY_DIR}/stage0.5/lib/lean/libleancpp.a" ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage0 stage0.5
  EXCLUDE_FROM_ALL ON
)
ExternalProject_add(stage2
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage2
  CMAKE_ARGS -DSTAGE=2 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage1 -DLEANCPP="${CMAKE_BINARY_DIR}/stage0.5/lib/lean/libleancpp.a" ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage1
  EXCLUDE_FROM_ALL ON
)
ExternalProject_add(stage3
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage3
  CMAKE_ARGS -DSTAGE=3 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage2 -DLEANCPP="${CMAKE_BINARY_DIR}/stage0.5/lib/lean/libleancpp.a" ${CL_ARGS}
  # skip building library - if `lean` is the same as in stage2, the library will be as well
  BUILD_COMMAND $(MAKE) lean
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage2
  EXCLUDE_FROM_ALL ON
)

# targets forwarded to appropriate stages

add_custom_target(update-stage0
  COMMAND $(MAKE) -C stage0 update-stage0
  DEPENDS stage0)

add_custom_target(test
  COMMAND $(MAKE) -C stage0.5 test
  DEPENDS stage0.5)

install(CODE "execute_process(COMMAND make -C stage0.5 install)")

add_custom_target(check-stage3
  COMMAND diff "stage2/bin/lean" "stage3/bin/lean"
  DEPENDS stage3)

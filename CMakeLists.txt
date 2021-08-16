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
  if(("${var}" MATCHES "CMAKE_.*") AND NOT ("${var}" MATCHES "CMAKE_BUILD_TYPE") AND NOT ("${var}" MATCHES "CMAKE_HOME_DIRECTORY"))
    list(APPEND PLATFORM_ARGS "-D${var}=${${var}}")
  endif()
endforeach()

include(ExternalProject)
project(LEAN CXX C)

if("${CMAKE_SYSTEM_NAME}" MATCHES "Emscripten")
  # For Emscripten, we build GMP before any of the stages and reuse it in all of them.
  set(GMP_INSTALL_PREFIX ${CMAKE_BINARY_DIR}/gmp-root)
  set(EMSCRIPTEN_FLAGS "-s ALLOW_MEMORY_GROWTH=1 -s MAIN_MODULE=1 -O3")
  ExternalProject_Add(
    gmp
    URL https://gmplib.org/download/gmp/gmp-6.2.1.tar.bz2
    URL_HASH SHA256=eae9326beb4158c386e39a356818031bd28f3124cf915f8c5b1dc4c7a36b4d7c
    BUILD_IN_SOURCE 1
    CONFIGURE_COMMAND emconfigure ./configure "CFLAGS=${EMSCRIPTEN_FLAGS}" --host=wasm32-unknown-emscripten --disable-assembly --prefix=${GMP_INSTALL_PREFIX}
    BUILD_COMMAND emmake make -j4
    INSTALL_COMMAND emmake make install
  )
  set(EXTRA_DEPENDS "gmp")
  list(APPEND CL_ARGS "-DGMP_INSTALL_PREFIX=${GMP_INSTALL_PREFIX}")
  list(APPEND PLATFORM_ARGS "-DGMP_INSTALL_PREFIX=${GMP_INSTALL_PREFIX}")
endif()
ExternalProject_add(stage0
  SOURCE_DIR "${LEAN_SOURCE_DIR}/stage0"
  SOURCE_SUBDIR src
  BINARY_DIR stage0
  # always use standard release build (discarding LEAN_CXX_EXTRA_FLAGS etc.) for stage0 since it is assumed to be "good", but still pass through CMake platform arguments (compiler, toolchain file, ..)
  # do not rebuild stage0 when git hash changes; it's not from this commit anyway
  CMAKE_ARGS -DSTAGE=0 -DCMAKE_BUILD_TYPE=Release -DUSE_GITHASH=OFF ${PLATFORM_ARGS}
  BUILD_ALWAYS ON  # cmake doesn't auto-detect changes without a download method
  INSTALL_COMMAND ""  # skip install
  DEPENDS ${EXTRA_DEPENDS}
)
ExternalProject_add(stage1
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage1
  CMAKE_ARGS -DSTAGE=1 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage0 ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage0
)
ExternalProject_add(stage2
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage2
  CMAKE_ARGS -DSTAGE=2 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage1 ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage1
  EXCLUDE_FROM_ALL ON
)
ExternalProject_add(stage3
  SOURCE_DIR "${LEAN_SOURCE_DIR}"
  SOURCE_SUBDIR src
  BINARY_DIR stage3
  CMAKE_ARGS -DSTAGE=3 -DPREV_STAGE=${CMAKE_BINARY_DIR}/stage2 ${CL_ARGS}
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  DEPENDS stage2
  EXCLUDE_FROM_ALL ON
)

# targets forwarded to appropriate stages

add_custom_target(update-stage0
  COMMAND $(MAKE) -C stage1 update-stage0
  DEPENDS stage1)

add_custom_target(test
  COMMAND $(MAKE) -C stage1 test
  DEPENDS stage1)

install(CODE "execute_process(COMMAND make -C stage1 install)")

add_custom_target(check-stage3
  COMMAND diff "stage2/bin/lean" "stage3/bin/lean"
  DEPENDS stage3)

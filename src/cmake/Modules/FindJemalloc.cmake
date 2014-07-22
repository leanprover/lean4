if (JEMALLOC_INCLUDE_DIR AND JEMALLOC_LIBRARIES)
  # Already in cache, be silent
  set(JEMALLOC_FIND_QUIETLY TRUE)
endif (JEMALLOC_INCLUDE_DIR AND JEMALLOC_LIBRARIES)

find_path(JEMALLOC_INCLUDE_DIR NAMES jemalloc/jemalloc.h)
find_library(JEMALLOC_LIBRARIES NAMES jemalloc)

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(JEMALLOC DEFAULT_MSG JEMALLOC_INCLUDE_DIR JEMALLOC_LIBRARIES)

# Print out version number
if (JEMALLOC_FOUND)
  try_run(JE_CHECK JE_CHECK_BUILD
    ${LEAN_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp
    ${LEAN_SOURCE_DIR}/cmake/Modules/CheckJemalloc.cc
    CMAKE_FLAGS -DINCLUDE_DIRECTORIES=${JEMALLOC_INCLUDE_DIR}
    -DLINK_LIBRARIES=${JEMALLOC_LIBRARIES}
    RUN_OUTPUT_VARIABLE JE_TRY_OUT)
  message("-- Found JEMALLOC: version ${JE_TRY_OUT}")
else ()
  message("*** WARNING: failed to find jemalloc")
  message("*** The (optional) jemalloc library is available at: https://github.com/jemalloc/jemalloc")
endif ()

mark_as_advanced(JEMALLOC_INCLUDE_DIR JEMALLOC_LIBRARIES)

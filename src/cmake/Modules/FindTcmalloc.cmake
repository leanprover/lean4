if (TCMALLOC_INCLUDE_DIR AND TCMALLOC_LIBRARIES)
  # Already in cache, be silent
  set(TCMALLOC_FIND_QUIETLY TRUE)
endif (TCMALLOC_INCLUDE_DIR AND TCMALLOC_LIBRARIES)

find_path(TCMALLOC_INCLUDE_DIR NAMES google/tcmalloc.h)
find_library(TCMALLOC_LIBRARIES NAMES tcmalloc)

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(TCMALLOC DEFAULT_MSG TCMALLOC_INCLUDE_DIR TCMALLOC_LIBRARIES)

# Print out version number
if (TCMALLOC_FOUND)
  try_run(TC_CHECK TC_CHECK_BUILD
    ${LEAN_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp
    ${LEAN_SOURCE_DIR}/cmake/Modules/CheckTcmalloc.cc
    CMAKE_FLAGS -DINCLUDE_DIRECTORIES=${TCMALLOC_INCLUDE_DIR}
    -DLINK_LIBRARIES=${TCMALLOC_LIBRARIES}
    RUN_OUTPUT_VARIABLE TC_TRY_OUT)
  message("-- Found TCMALLOC: version ${TC_TRY_OUT}")
else ()
  message("*** WARNING: failed to find tcmalloc")
  message("*** The (optional) tcmalloc library is available at: https://code.google.com/p/gperftools")
endif ()

mark_as_advanced(TCMALLOC_INCLUDE_DIR TCMALLOC_LIBRARIES)

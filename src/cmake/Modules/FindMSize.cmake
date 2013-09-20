find_path(MALLOC_DIR NAMES malloc.h )

try_run(MSIZE_CHECK MSIZE_CHECK_BUILD
  ${LEAN_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp
  ${LEAN_SOURCE_DIR}/cmake/Modules/CheckMSize.cc
  CMAKE_FLAGS -DINCLUDE_DIRECTORIES=${MALLOC_DIR}
  RUN_OUTPUT_VARIABLE MSIZE_TRY_OUT)

if("${MSIZE_CHECK_BUILD}" MATCHES "TRUE" AND "${MSIZE_CHECK}" MATCHES "0")
  message(STATUS "Found malloc_usable_size")
  set(MSIZE_FOUND TRUE)
else()
  message(STATUS "Usable malloc_usable_size was not detected")
  set(MSIZE_FOUND FALSE)
endif()



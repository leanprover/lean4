find_path(MALLOC_DIR NAMES malloc.h )
if(NOT "${MALLOC_DIR}" MATCHES "MALLOC_DIR-NOTFOUND")
  try_run(MUS_CHECK MUS_CHECK_BUILD
    ${LEAN_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp
    ${LEAN_SOURCE_DIR}/cmake/Modules/CheckMallocUsableSize.cc
    CMAKE_FLAGS -DINCLUDE_DIRECTORIES=${MALLOC_DIR}
    RUN_OUTPUT_VARIABLE MUS_TRY_OUT)
  
  if("${MUS_CHECK_BUILD}" MATCHES "TRUE" AND "${MUS_CHECK}" MATCHES "0")
    message(STATUS "Found malloc_usable_size")
    set(MUS_FOUND TRUE)
  else()
    message(STATUS "Usable malloc_usable_size was not detected")
    set(MUS_FOUND FALSE)
  endif()
else()
  set(MUS_FOUND FALSE)
endif()

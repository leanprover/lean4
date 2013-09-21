find_path(MALLOC_DIR NAMES malloc.h )
if(NOT "${MALLOC_DIR}" MATCHES "MALLOC_DIR-NOTFOUND")
  if(CMAKE_CROSSCOMPILING)
    if("${CMAKE_SYSTEM_NAME}" MATCHES "Windows")
      # If it's cross-compilation and target is windows, first compile MSIZE_CHECK.exe
      execute_process(COMMAND ${CMAKE_CXX_COMPILER}
        "-o" ${LEAN_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/MSIZE_CHECK.exe
        ${LEAN_SOURCE_DIR}/cmake/Modules/CheckMSize.cc
        RESULT_VARIABLE MSIZE_CHECK_BUILD_RESULT)
      if("${MSIZE_CHECK_BUILD_RESULT}" MATCHES "0")
        set(MSIZE_CHECK_BUILD "TRUE")
        # Check whether "wine" exists to run "MSIZE_CHECK.exe"
        execute_process(COMMAND "bash" "-c" "wine --version > /dev/null 2&>1"
                        RESULT_VARIABLE WINE_CHECK)
        if("${WINE_CHECK}" MATCHES "0")
          execute_process(COMMAND "wine"
            ${LEAN_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp/MSIZE_CHECK.exe
            RESULT_VARIABLE MSIZE_CHECK)
        else()
          # NOTE: We can compile a progrm with _msize, but we can't test
          # it due to the lack of wine. We assume that it is usable
          set(MSIZE_CHECK "0")
          set(MSIZE_UNTESTED "(untested)")
        endif()
      else()
        set(MSIZE_CHECK_BUILD "FALSE")
      endif()
    else()
      # It's cross-compilation but the target is not Windows
      set(MSIZE_FOUND FALSE)
    endif()
  else()
    try_run(MSIZE_CHECK MSIZE_CHECK_BUILD
      ${LEAN_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/CMakeTmp
      ${LEAN_SOURCE_DIR}/cmake/Modules/CheckMSize.cc
      CMAKE_FLAGS -DINCLUDE_DIRECTORIES=${MALLOC_DIR}
      RUN_OUTPUT_VARIABLE MSIZE_TRY_OUT)
  endif()
  
  if("${MSIZE_CHECK_BUILD}" MATCHES "TRUE" AND "${MSIZE_CHECK}" MATCHES "0")
    message(STATUS "Found _msize " "${MSIZE_UNTESTED}")
    set(MSIZE_FOUND TRUE)
  else()
    message(STATUS "Usable _msize was not detected")
    set(MSIZE_FOUND FALSE)
  endif()
else()
  set(MSIZE_FOUND FALSE)
endif()

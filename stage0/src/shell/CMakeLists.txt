if(PREV_STAGE)
  string(TOUPPER "${CMAKE_BUILD_TYPE}" uppercase_CMAKE_BUILD_TYPE)
  set(LEANC_OPTS "${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}}")

  add_custom_target(make_stdlib
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}"
    COMMAND bash -c "PATH=${PREV_STAGE}/bin:$$PATH $(MAKE) -f ${CMAKE_BINARY_DIR}/share/lean/Makefile OUT=${CMAKE_BINARY_DIR}/lib MORE_DEPS=${PREV_STAGE}/bin/lean")
  set_target_properties(leanstdlib PROPERTIES
    IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/lib/libleanstdlib.a"
    IMPORTED_LINK_INTERFACE_LIBRARIES leanstatic)
  add_dependencies(leanstdlib make_stdlib)
  install(FILES "$<TARGET_FILE:leanstdlib>" DESTINATION lib)
endif()

add_executable(lean lean.cpp)
set_target_properties(lean PROPERTIES RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")

# `leanstatic` and `leanstdlib` are cyclically dependent static libraries.
# We use the approach described at
# https://cmake.org/cmake/help/v3.3/command/target_link_libraries.html#cyclic-dependencies-of-static-libraries
# We don't want to add leanstdlib as a direct dependency of leanstatic since this is only true for stage 1.
target_link_libraries(lean leanstatic leanstdlib leanstatic leanstdlib)

# create import library on Windows to link plugins against
set_target_properties(lean PROPERTIES ENABLE_EXPORTS ON)
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
  # https://github.com/msys2/MINGW-packages/issues/5952
  target_link_options(lean PRIVATE "-Wl,--out-implib,$<TARGET_LINKER_FILE:lean>")
endif()
install(TARGETS lean DESTINATION bin)

# add_test(example1_stdin1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_BINARY_DIR}/bin/lean "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(lean_export ${CMAKE_BINARY_DIR}/bin/lean "-o simple.olean" "${LEAN_SOURCE_DIR}/../tests/lean/run/simple.lean")
add_test(lean_help1    "${CMAKE_BINARY_DIR}/bin/lean" --help)
add_test(lean_help2    "${CMAKE_BINARY_DIR}/bin/lean" -h)
add_test(lean_version1 "${CMAKE_BINARY_DIR}/bin/lean" --version)
if (NOT ${EMSCRIPTEN})
add_test(lean_version2 "${CMAKE_BINARY_DIR}/bin/lean" --v)
endif()
add_test(lean_ghash1   "${CMAKE_BINARY_DIR}/bin/lean" -g)
add_test(lean_ghash2   "${CMAKE_BINARY_DIR}/bin/lean" --githash)
# add_test(lean_new_frontend "${CMAKE_BINARY_DIR}/bin/lean" --new-frontend "${LEAN_SOURCE_DIR}/Init/Core.lean")
add_test(lean_unknown_option bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_BINARY_DIR}/bin/lean" "-z")
add_test(lean_unknown_file1 bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_BINARY_DIR}/bin/lean" "boofoo.lean")

# LEAN TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
FOREACH(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leantest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
             COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

# LEAN RUN TESTS
file(GLOB LEANRUNTESTS "${LEAN_SOURCE_DIR}/../tests/lean/run/*.lean")
FOREACH(T ${LEANRUNTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leanruntest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/run"
             COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

# LEAN new frontend TESTS
file(GLOB LEANNEWFRONTENDTESTS "${LEAN_SOURCE_DIR}/../tests/lean/newfrontend/*.lean")
FOREACH(T ${LEANNEWFRONTENDTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leannewfrontendtest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/newfrontend"
             COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

# LEAN COMPILER TESTS
file(GLOB LEANCOMPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
FOREACH(T ${LEANCOMPTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leancomptest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
           COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T)

# LEAN INTERPRETER TESTS
file(GLOB LEANINTERPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
FOREACH(T ${LEANINTERPTESTS})
  if(NOT EXISTS "${T}.no_interpreter")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leaninterptest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
             COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single_interpret.sh ${T_NAME}")
  endif()
ENDFOREACH(T)

# LEAN BENCHMARK TESTS
# do not test all .lean files in bench/
file(GLOB LEANBENCHTESTS "${LEAN_SOURCE_DIR}/../tests/bench/*.lean.expected.out")
FOREACH(T_OUT ${LEANBENCHTESTS})
  string(REPLACE ".expected.out" "" T ${T_OUT})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanbenchtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/bench"
           COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T_OUT)

# LEAN PLUGIN TESTS
file(GLOB LEANINTERPTESTS "${LEAN_SOURCE_DIR}/../tests/plugin/*.lean")
FOREACH(T ${LEANINTERPTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanplugintest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/plugin"
           COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T)

# LEAN TESTS using --trust=0
file(GLOB LEANT0TESTS "${LEAN_SOURCE_DIR}/../tests/lean/trust0/*.lean")
FOREACH(T ${LEANT0TESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leant0test_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/trust0"
           COMMAND bash -c "PATH=${CMAKE_BINARY_DIR}/bin:$PATH ./test_single.sh ${T_NAME}")
ENDFOREACH(T)

# MSYS2 bash usually handles Windows paths relatively well, but not when putting them in the PATH
string(REGEX REPLACE "^([a-zA-Z]):" "/\\1" LEAN_BIN "${CMAKE_BINARY_DIR}/bin")

# Environment variables
set(TEST_VARS "${LEAN_TEST_VARS}")
string(APPEND TEST_VARS " PATH=${LEAN_BIN}:\$PATH")
string(APPEND TEST_VARS " LEANC_OPTS='${LEANC_OPTS}'")
# LEANC_OPTS in CXX is necessary for macOS c++ to find its headers
string(APPEND TEST_VARS " CXX='${CMAKE_CXX_COMPILER} ${LEANC_OPTS}'")

add_test(lean_help1 "${CMAKE_BINARY_DIR}/bin/lean" --help)
add_test(lean_help2 "${CMAKE_BINARY_DIR}/bin/lean" -h)
add_test(lean_version1 "${CMAKE_BINARY_DIR}/bin/lean" --version)
add_test(lean_version2 "${CMAKE_BINARY_DIR}/bin/lean" --v)
add_test(lean_ghash1 "${CMAKE_BINARY_DIR}/bin/lean" -g)
add_test(lean_ghash2 "${CMAKE_BINARY_DIR}/bin/lean" --githash)
add_test(lean_unknown_option bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_BINARY_DIR}/bin/lean" "-z")
add_test(
  lean_unknown_file1
  bash
  "${LEAN_SOURCE_DIR}/cmake/check_failure.sh"
  "${CMAKE_BINARY_DIR}/bin/lean"
  "boofoo.lean"
)

# LEAN TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
foreach(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
      COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
    )
  endif()
endforeach(T)

# LEAN RUN TESTS
file(GLOB LEANRUNTESTS "${LEAN_SOURCE_DIR}/../tests/lean/run/*.lean")
foreach(T ${LEANRUNTESTS})
  if(NOT T MATCHES "\\.#")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/run"
      COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
    )
  endif()
endforeach(T)

# LEAN RUN doc/examples
file(GLOB LEANDOCEXS "${LEAN_SOURCE_DIR}/../doc/examples/*.lean")
foreach(T ${LEANDOCEXS})
  if(NOT T MATCHES "\\.#")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/examples"
      COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
    )
  endif()
endforeach(T)

# LEAN COMPILER TESTS
file(GLOB LEANCOMPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
foreach(T ${LEANCOMPTESTS})
  get_filename_component(T_NAME ${T} NAME)
  cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
  add_test(
    NAME "${T_PATH}"
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
    COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
  )
endforeach(T)

add_test(
  NAME leancomptest_foreign
  WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler/foreign"
  COMMAND bash -c "${LEAN_BIN}/leanmake --always-make"
)
add_test(
  NAME leancomptest_doc_example
  WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/examples/compiler"
  COMMAND bash -c "export ${TEST_VARS}; leanmake --always-make bin && ./build/bin/test hello world"
)

# LEAN INTERPRETER TESTS
file(GLOB LEANINTERPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
foreach(T ${LEANINTERPTESTS})
  if(NOT EXISTS "${T}.no_interpreter")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH} (interpreted)"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
      COMMAND bash -c "${TEST_VARS} ./test_single_interpret.sh ${T_NAME}"
    )
  endif()
endforeach(T)

# LEAN BENCHMARK TESTS
# do not test all .lean files in bench/
file(GLOB LEANBENCHTESTS "${LEAN_SOURCE_DIR}/../tests/bench/*.lean.expected.out")
foreach(T_OUT ${LEANBENCHTESTS})
  string(REPLACE ".expected.out" "" T ${T_OUT})
  get_filename_component(T_NAME ${T} NAME)
  cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
  add_test(
    NAME "${T_PATH}"
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/bench"
    COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
  )
endforeach(T_OUT)

file(GLOB LEANINTERPTESTS "${LEAN_SOURCE_DIR}/../tests/plugin/*.lean")
foreach(T ${LEANINTERPTESTS})
  get_filename_component(T_NAME ${T} NAME)
  cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
  add_test(
    NAME "${T_PATH}"
    WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/plugin"
    COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
  )
endforeach(T)

# LEAN PACKAGE TESTS
file(GLOB LEANPKGTESTS "${LEAN_SOURCE_DIR}/../tests/pkg/*")
foreach(T ${LEANPKGTESTS})
  if(EXISTS "${T}/test.sh")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(NAME "${T_PATH}" WORKING_DIRECTORY "${T}" COMMAND bash -c "${TEST_VARS} ./test.sh")
  endif()
endforeach(T)

# LEAN SERVER TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/server/*.lean")
foreach(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/server"
      COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
    )
  endif()
endforeach(T)

# LEAN INTERACTIVE SERVER TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/interactive/*.lean")
foreach(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#" AND NOT T MATCHES "run.lean")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/interactive"
      COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
    )
  endif()
endforeach(T)

# LEAN INTERACTIVE PROJECT SERVER TESTS
file(GLOB_RECURSE LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/interactive/projects/*Test.lean")
foreach(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/interactive/projects"
      COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T}"
    )
  endif()
endforeach(T)

# LEAN DOCSTRING PARSER TESTS
file(GLOB_RECURSE LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/docparse/*_[0-9][0-9][0-9][0-9]")
foreach(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#" AND NOT T MATCHES "run.lean")
    get_filename_component(T_NAME ${T} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/docparse"
      COMMAND bash -c "${TEST_VARS} ./test_single.sh ${T_NAME}"
    )
  endif()
endforeach(T)

# Create a lake test for each test and examples subdirectory of `lake`
# which contains a `test.sh` file, excluding the following test(s):
# bootstrap: too slow
# toolchain: requires elan to download toolchain
# online: downloads remote repositories
file(
  GLOB_RECURSE LEANLAKETESTS
  #"${LEAN_SOURCE_DIR}/../tests/lake/tests/test.sh"
  "${LEAN_SOURCE_DIR}/../tests/lake/examples/test.sh"
  "${LEAN_SOURCE_DIR}/../tests/lake/tests/shake/test.sh"
)
foreach(T ${LEANLAKETESTS})
  if(NOT T MATCHES ".*(lake-packages|bootstrap|toolchain|online).*")
    get_filename_component(T_DIR ${T} DIRECTORY)
    get_filename_component(DIR_NAME ${T_DIR} NAME)
    cmake_path(RELATIVE_PATH T BASE_DIRECTORY ${LEAN_SOURCE_DIR}/.. OUTPUT_VARIABLE T_PATH)
    add_test(
      NAME "${T_PATH}"
      WORKING_DIRECTORY "${T_DIR}"
      COMMAND
        bash -c
        "
               set -eu
               export ${TEST_VARS}
               LAKE=lake ./test.sh"
    )
  endif()
endforeach(T)

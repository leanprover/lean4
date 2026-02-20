#################
## Environment ##
#################

# MSYS2 bash usually handles Windows paths relatively well, but not when putting them in the PATH
string(REGEX REPLACE "^([a-zA-Z]):" "/\\1" LEAN_BIN "${CMAKE_BINARY_DIR}/bin")

set(TEST_VARS "${LEAN_TEST_VARS}")

# Test scripts can use these to find other parts of the repo, e.g. "$TEST_DIR/measure.py"
string(APPEND TEST_VARS " STAGE='${STAGE}'") # Using this should not normally be necessary
string(APPEND TEST_VARS " SRC_DIR='${CMAKE_SOURCE_DIR}'")
string(APPEND TEST_VARS " TEST_DIR='${CMAKE_CURRENT_SOURCE_DIR}'")
string(APPEND TEST_VARS " BUILD_DIR='${CMAKE_BINARY_DIR}'")
string(APPEND TEST_VARS " SCRIPT_DIR='${CMAKE_SOURCE_DIR}/../script'")

# Use the current stage's lean binary instead of whatever lake thinks we want
string(APPEND TEST_VARS " PATH='${LEAN_BIN}':\"$PATH\"")

string(APPEND TEST_VARS " LEANC_OPTS='${LEANC_OPTS}'")

# LEANC_OPTS in CXX is necessary for macOS c++ to find its headers
string(APPEND TEST_VARS " CXX='${CMAKE_CXX_COMPILER} ${LEANC_OPTS}'")

string(APPEND TEST_VARS " TEST_BENCH=")
configure_file(env.sh.in "${CMAKE_CURRENT_SOURCE_DIR}/env_test.sh")

block()
  string(APPEND TEST_VARS " TEST_BENCH=1")
  configure_file(env.sh.in "${CMAKE_CURRENT_SOURCE_DIR}/env_bench.sh")
endblock()

######################
## Helper functions ##
######################

function(check_test_bench_scripts DIR DIR_ABS)
  set(RUN_TEST "${DIR_ABS}/run_test")
  set(RUN_BENCH "${DIR_ABS}/run_bench")

  set(RUN_TEST_EXISTS FALSE)
  set(RUN_BENCH_EXISTS FALSE)
  if(EXISTS "${RUN_TEST}")
    set(RUN_TEST_EXISTS TRUE)
  endif()
  if(EXISTS "${RUN_BENCH}")
    set(RUN_BENCH_EXISTS TRUE)
  endif()

  if(NOT RUN_TEST_EXISTS AND NOT RUN_BENCH_EXISTS)
    message(FATAL_ERROR "${DIR}: Found neither a run_test nor a run_bench file")
    return()
  endif()

  # Replace with return(PROPAGATE) if we ever update to cmake 3.25+
  set(RUN_TEST "${RUN_TEST}" PARENT_SCOPE)
  set(RUN_BENCH "${RUN_BENCH}" PARENT_SCOPE)
  set(RUN_TEST_EXISTS "${RUN_TEST_EXISTS}" PARENT_SCOPE)
  set(RUN_BENCH_EXISTS "${RUN_BENCH_EXISTS}" PARENT_SCOPE)
endfunction()

function(check_bench_argument DIR ARGS_BENCH RUN_BENCH_EXISTS)
  if(RUN_BENCH_EXISTS AND NOT ARGS_BENCH)
    message(FATAL_ERROR "${DIR}: run_bench file found, BENCH argument must be specified")
    return()
  endif()
  if(NOT RUN_BENCH_EXISTS AND ARGS_BENCH)
    message(FATAL_ERROR "${DIR}: BENCH argument specified but no run_bench file found")
    return()
  endif()
endfunction()

function(add_combined_measurements OUTPUT)
  if(NOT ARGN)
    message(AUTHOR_WARNING "No input measurements provided for ${OUTPUT}")
    add_custom_command(OUTPUT "${OUTPUT}" COMMAND "${CMAKE_COMMAND}" -E touch "${OUTPUT}")
    return()
  endif()

  add_custom_command(
    OUTPUT "${OUTPUT}"
    DEPENDS "${ARGN}"
    COMMAND "${CMAKE_CURRENT_SOURCE_DIR}/combine.py" -o "${OUTPUT}" -- ${ARGN}
  )
endfunction()

# A test pile is a directory containing many test files, each of which
# represents a separate test (or benchmark). The directory may also contain
# additional files or subdirectories required by the individual test files.
#
# If a run_test script is present, each test file will be added as a test. Tests
# can be disabled on a per-file basis by creating a `<file>.no_test` file.
#
# If a run_bench script is present, each test file will be added as a benchmark.
# Benchmarks can be disabled on a per-file basis by creating a `<file>.no_bench`
# file. CMake expects the bench script to produce a `<file>.measurements.jsonl`
# file next to the test file. The individual measurements will be combined into
# a single `measurements.jsonl` file in the pile directory, whose path will be
# added to the list specified by the BENCH argument.
function(add_test_pile DIR GLOB)
  cmake_parse_arguments(ARGS "" BENCH "" ${ARGN})
  set(DIR_ABS "${CMAKE_CURRENT_SOURCE_DIR}/${DIR}")

  check_test_bench_scripts("${DIR}" "${DIR_ABS}")
  check_bench_argument("${DIR}" "${ARGS_BENCH}" "${RUN_BENCH_EXISTS}")

  # The test files' individual measurement files that will later be combined
  # into a single measurements.jsonl file
  set(MEASUREMENTS_FILES "")

  # Iterate over all files matching the glob
  file(GLOB TEST_FILES "${DIR_ABS}/${GLOB}")
  foreach(FILE_ABS IN LISTS TEST_FILES)
    # Path relative to source directory
    cmake_path(RELATIVE_PATH FILE_ABS BASE_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}" OUTPUT_VARIABLE FILE)
    # Path relative to pile directory
    cmake_path(RELATIVE_PATH FILE_ABS BASE_DIRECTORY "${DIR_ABS}" OUTPUT_VARIABLE FILE_NAME)

    if(RUN_TEST_EXISTS AND NOT EXISTS "${FILE_ABS}.no_test")
      add_test(NAME "${FILE}" WORKING_DIRECTORY "${DIR_ABS}" COMMAND "${RUN_TEST}" "${FILE_NAME}")
    endif()

    if(RUN_BENCH_EXISTS AND NOT EXISTS "${FILE_ABS}.no_bench")
      set(MEASUREMENTS_FILE "${FILE_ABS}.measurements.jsonl")
      list(APPEND MEASUREMENTS_FILES "${MEASUREMENTS_FILE}")
      add_custom_command(
        OUTPUT "${MEASUREMENTS_FILE}"
        WORKING_DIRECTORY "${DIR_ABS}"
        COMMAND "${CMAKE_COMMAND}" -E remove -f "${MEASUREMENTS_FILE}"
        COMMAND "${RUN_BENCH}" "${FILE_NAME}"
      )
    endif()
  endforeach()

  # Combine measurements
  if(RUN_BENCH_EXISTS)
    set(MEASUREMENTS_FILE "${DIR_ABS}/measurements.jsonl")
    list(APPEND "${ARGS_BENCH}" "${MEASUREMENTS_FILE}")
    set("${ARGS_BENCH}" "${${ARGS_BENCH}}" PARENT_SCOPE)
    add_combined_measurements("${MEASUREMENTS_FILE}" "${MEASUREMENTS_FILES}")
  endif()
endfunction()

# A test directory is a directory containing a single test (or benchmark),
# alongside any additional files or subdirectories required by that test.
function(add_test_dir DIR)
  cmake_parse_arguments(ARGS "" BENCH "" ${ARGN})
  set(DIR_ABS "${CMAKE_CURRENT_SOURCE_DIR}/${DIR}")

  check_test_bench_scripts("${DIR}" "${DIR_ABS}")
  check_bench_argument("${DIR}" "${ARGS_BENCH}" "${RUN_BENCH_EXISTS}")

  # Add as test
  if(RUN_TEST_EXISTS)
    add_test(NAME "${DIR}" WORKING_DIRECTORY "${DIR_ABS}" COMMAND "${RUN_TEST}")
  endif()

  # Add as benchmark
  if(RUN_BENCH_EXISTS)
    set(MEASUREMENTS_FILE "${DIR_ABS}/measurements.jsonl")
    list(APPEND "${ARGS_BENCH}" "${MEASUREMENTS_FILE}")
    set("${ARGS_BENCH}" "${${ARGS_BENCH}}" PARENT_SCOPE)
    add_custom_command(
      OUTPUT "${MEASUREMENTS_FILE}"
      WORKING_DIRECTORY "${DIR_ABS}"
      COMMAND "${CMAKE_COMMAND}" -E remove -f "${MEASUREMENTS_FILE}"
      COMMAND "${RUN_BENCH}"
    )
  endif()
endfunction()

# Benchmarks are split into two parts which should be roughly equal in total runtime.
# In radar, each part is run on a different runner.
set(PART1 "")
set(PART2 "")

##########################
## Tests and benchmarks ##
##########################

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

add_test_pile(compile *.lean BENCH PART2)
add_test_pile(compile_bench *.lean BENCH PART2)
add_test_pile(elab *.lean)
add_test_pile(elab_bench *.lean BENCH PART2)
add_test_pile(elab_fail *.lean)
add_test_pile(misc *.sh)
add_test_pile(misc_bench *.sh BENCH PART2)

add_test_dir(bench/build BENCH PART1)
add_test_dir(bench/size BENCH PART1)
add_test_dir(lake_bench/inundation BENCH PART2)

#######################
## Benchmark targets ##
#######################

set(BENCH_MEASUREMENTS_PART1 "${CMAKE_CURRENT_SOURCE_DIR}/part1.measurements.jsonl")
set(BENCH_MEASUREMENTS_PART2 "${CMAKE_CURRENT_SOURCE_DIR}/part2.measurements.jsonl")
set(BENCH_MEASUREMENTS "${CMAKE_CURRENT_SOURCE_DIR}/measurements.jsonl")

add_combined_measurements("${BENCH_MEASUREMENTS_PART1}" "${PART1}")
add_combined_measurements("${BENCH_MEASUREMENTS_PART2}" "${PART2}")
add_combined_measurements("${BENCH_MEASUREMENTS}" "${BENCH_MEASUREMENTS_PART1}" "${BENCH_MEASUREMENTS_PART2}")

add_custom_target(bench-part1 DEPENDS lean "${BENCH_MEASUREMENTS_PART1}" COMMENT "Run benchmarks (part 1)")
add_custom_target(bench-part2 DEPENDS lean "${BENCH_MEASUREMENTS_PART2}" COMMENT "Run benchmarks (part 2)")
add_custom_target(bench DEPENDS lean "${BENCH_MEASUREMENTS}" COMMENT "Run all benchmarks")

#################
## Environment ##
#################

# MSYS2 bash usually handles Windows paths relatively well, but not in all situations.
# Thus, rewrite C:/foo/bar to /C/foo/bar on Windows.
function(mangle_windows_path OUT PATH)
  if(WIN32)
    string(REGEX REPLACE "^([a-zA-Z]):" "/\\1" RESULT "${PATH}")
    # Replace with return(PROPAGATE) if we ever update to cmake 3.25+
    set("${OUT}" "${RESULT}" PARENT_SCOPE)
  else()
    # Replace with return(PROPAGATE) if we ever update to cmake 3.25+
    set("${OUT}" "${PATH}" PARENT_SCOPE)
  endif()
endfunction()

mangle_windows_path(MANGLED_BINARY_DIR "${CMAKE_BINARY_DIR}")
mangle_windows_path(MANGLED_SOURCE_DIR "${CMAKE_SOURCE_DIR}")
mangle_windows_path(MANGLED_CURRENT_SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}")

set(LEAN_BIN "${MANGLED_BINARY_DIR}/bin")

set(TEST_VARS "${LEAN_TEST_VARS}")

# Test scripts can use these to find other parts of the repo, e.g. "$TEST_DIR/measure.py"
string(APPEND TEST_VARS " STAGE='${STAGE}'") # Using this should not normally be necessary
string(APPEND TEST_VARS " SRC_DIR='${MANGLED_SOURCE_DIR}'")
string(APPEND TEST_VARS " TEST_DIR='${MANGLED_CURRENT_SOURCE_DIR}'")
string(APPEND TEST_VARS " BUILD_DIR='${MANGLED_BINARY_DIR}'")
string(APPEND TEST_VARS " SCRIPT_DIR='${MANGLED_SOURCE_DIR}/../script'")

# Use the current stage's lean binary instead of whatever lake thinks we want
string(APPEND TEST_VARS " PATH='${LEAN_BIN}':\"$PATH\"")

string(APPEND TEST_VARS " LEANC_OPTS='${LEANC_OPTS}'")

# LEANC_OPTS in CXX is necessary for macOS c++ to find its headers
string(APPEND TEST_VARS " CXX='${CMAKE_CXX_COMPILER} ${LEANC_OPTS}'")

set(WITH_TEST_ENV "${CMAKE_CURRENT_SOURCE_DIR}/with_stage${STAGE}_test_env.sh")
set(WITH_BENCH_ENV "${CMAKE_CURRENT_SOURCE_DIR}/with_stage${STAGE}_bench_env.sh")

configure_file(with_env.sh.in "${WITH_TEST_ENV}")

block()
  string(APPEND TEST_VARS " TEST_BENCH=1")
  configure_file(with_env.sh.in "${WITH_BENCH_ENV}")
endblock()

######################
## Helper functions ##
######################

function(glob_except OUT DIR GLOB)
  cmake_parse_arguments(ARGS "" "" EXCEPT ${ARGN})
  cmake_path(ABSOLUTE_PATH DIR NORMALIZE)

  file(GLOB ALL_FILES "${DIR}/${GLOB}")
  set(RETAINED_FILES "")

  foreach(FILE IN LISTS ALL_FILES)
    cmake_path(RELATIVE_PATH FILE BASE_DIRECTORY "${DIR}" OUTPUT_VARIABLE FILE_IN_DIR)
    if(NOT FILE_IN_DIR IN_LIST ARGS_EXCEPT)
      list(APPEND RETAINED_FILES "${FILE}")
    endif()
  endforeach()

  # Replace with return(PROPAGATE) if we ever update to cmake 3.25+
  set("${OUT}" "${RETAINED_FILES}" PARENT_SCOPE)
endfunction()

function(check_test_bench_scripts DIR)
  set(RUN_TEST "${DIR}/run_test.sh")
  set(RUN_BENCH "${DIR}/run_bench.sh")

  set(RUN_TEST_EXISTS FALSE)
  set(RUN_BENCH_EXISTS FALSE)
  if(EXISTS "${RUN_TEST}")
    set(RUN_TEST_EXISTS TRUE)
  endif()
  if(EXISTS "${RUN_BENCH}")
    set(RUN_BENCH_EXISTS TRUE)
  endif()

  if(NOT RUN_TEST_EXISTS AND NOT RUN_BENCH_EXISTS)
    cmake_path(RELATIVE_PATH DIR)
    message(AUTHOR_WARNING "${DIR}: Found neither a run_test nor a run_bench file")
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
    cmake_path(RELATIVE_PATH DIR)
    message(FATAL_ERROR "${DIR}: run_bench file found, BENCH argument must be specified")
    return()
  endif()
  if(NOT RUN_BENCH_EXISTS AND ARGS_BENCH)
    cmake_path(RELATIVE_PATH DIR)
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
# If a run_test.sh script is present, each test file will be added as a test. Tests
# can be disabled on a per-file basis by creating a `<file>.no_test` file.
#
# If a run_bench.sh script is present, each test file will be added as a benchmark.
# Benchmarks can be disabled on a per-file basis by creating a `<file>.no_bench`
# file. CMake expects the bench script to produce a `<file>.measurements.jsonl`
# file next to the test file. The individual measurements will be combined into
# a single `measurements.jsonl` file in the pile directory, whose path will be
# added to the list specified by the BENCH argument.
function(add_test_pile DIR GLOB)
  cmake_parse_arguments(ARGS "" BENCH EXCEPT ${ARGN})
  cmake_path(ABSOLUTE_PATH DIR NORMALIZE)

  check_test_bench_scripts("${DIR}")
  check_bench_argument("${DIR}" "${ARGS_BENCH}" "${RUN_BENCH_EXISTS}")

  # The test files' individual measurement files that will later be combined
  # into a single measurements.jsonl file
  set(MEASUREMENTS_FILES "")

  # Iterate over all files matching the glob
  glob_except(TEST_FILES "${DIR}" "${GLOB}" EXCEPT "${ARGS_EXCEPT}")
  foreach(FILE IN LISTS TEST_FILES)
    cmake_path(RELATIVE_PATH FILE OUTPUT_VARIABLE FILE_IN_SOURCE_DIR)
    cmake_path(RELATIVE_PATH FILE BASE_DIRECTORY "${DIR}" OUTPUT_VARIABLE FILE_IN_DIR)

    if(FILE_IN_DIR MATCHES "^run_(test|bench)")
      continue()
    endif()

    if(RUN_TEST_EXISTS AND NOT EXISTS "${FILE}.no_test")
      add_test(
        NAME "${FILE_IN_SOURCE_DIR}"
        WORKING_DIRECTORY "${DIR}"
        # On Windows, we can't call the file directly, hence we always use bash.
        COMMAND bash "${WITH_TEST_ENV}" "${RUN_TEST}" "${FILE_IN_DIR}"
      )
    endif()

    if(RUN_BENCH_EXISTS AND NOT EXISTS "${FILE}.no_bench")
      set(MEASUREMENTS_FILE "${FILE}.measurements.jsonl")
      list(APPEND MEASUREMENTS_FILES "${MEASUREMENTS_FILE}")
      add_custom_command(
        OUTPUT "${MEASUREMENTS_FILE}"
        WORKING_DIRECTORY "${DIR}"
        COMMAND "${CMAKE_COMMAND}" -E remove -f "${MEASUREMENTS_FILE}"
        # On Windows, we can't call the file directly, hence we always use bash.
        COMMAND bash "${WITH_BENCH_ENV}" "${RUN_BENCH}" "${FILE_IN_DIR}"
      )
    endif()
  endforeach()

  # Combine measurements
  if(RUN_BENCH_EXISTS)
    set(MEASUREMENTS_FILE "${DIR}/measurements.jsonl")
    list(APPEND "${ARGS_BENCH}" "${MEASUREMENTS_FILE}")
    set("${ARGS_BENCH}" "${${ARGS_BENCH}}" PARENT_SCOPE)
    add_combined_measurements("${MEASUREMENTS_FILE}" "${MEASUREMENTS_FILES}")
  endif()
endfunction()

# A test directory is a directory containing a single test (or benchmark),
# alongside any additional files or subdirectories required by that test.
function(add_test_dir DIR)
  cmake_parse_arguments(ARGS "" BENCH "" ${ARGN})
  cmake_path(ABSOLUTE_PATH DIR NORMALIZE)

  check_test_bench_scripts("${DIR}")
  check_bench_argument("${DIR}" "${ARGS_BENCH}" "${RUN_BENCH_EXISTS}")

  # Add as test
  if(RUN_TEST_EXISTS)
    cmake_path(RELATIVE_PATH DIR OUTPUT_VARIABLE DIR_IN_SOURCE_DIR)
    add_test(
      NAME "${DIR_IN_SOURCE_DIR}"
      WORKING_DIRECTORY "${DIR}"
      # On Windows, we can't call the file directly, hence we always use bash.
      COMMAND bash "${WITH_TEST_ENV}" "${RUN_TEST}"
    )
  endif()

  # Add as benchmark
  if(RUN_BENCH_EXISTS)
    set(MEASUREMENTS_FILE "${DIR}/measurements.jsonl")
    list(APPEND "${ARGS_BENCH}" "${MEASUREMENTS_FILE}")
    set("${ARGS_BENCH}" "${${ARGS_BENCH}}" PARENT_SCOPE)
    add_custom_command(
      OUTPUT "${MEASUREMENTS_FILE}"
      WORKING_DIRECTORY "${DIR}"
      COMMAND "${CMAKE_COMMAND}" -E remove -f "${MEASUREMENTS_FILE}"
      # On Windows, we can't call the file directly, hence we always use bash.
      COMMAND bash "${WITH_BENCH_ENV}" "${RUN_BENCH}"
    )
  endif()
endfunction()

function(add_dir_of_test_dirs DIR)
  cmake_parse_arguments(ARGS "" "" EXCEPT ${ARGN})
  cmake_path(ABSOLUTE_PATH DIR NORMALIZE)

  glob_except(TEST_DIRS "${DIR}" "*" EXCEPT "${ARGS_EXCEPT}")
  foreach(TEST_DIR IN LISTS TEST_DIRS)
    if(IS_DIRECTORY "${TEST_DIR}")
      add_test_dir("${TEST_DIR}")
    endif()
  endforeach()
endfunction()

# Benchmarks are split into two parts which should be roughly equal in total runtime.
# In radar, each part is run on a different runner.
set(PART1 "")
set(PART2 "")

##########################
## Tests and benchmarks ##
##########################

# Create a lake test for each test and examples subdirectory of `lake`
# which contains a `test.sh` file, excluding the following test(s):
# bootstrap: too slow
# toolchain: requires elan to download toolchain
# online: downloads remote repositories
option(LAKE_CI "Enable full Lake test suite (use `lake-ci` label on PRs)" OFF)
if(LAKE_CI)
  file(
    GLOB_RECURSE LEANLAKETESTS
    "${LEAN_SOURCE_DIR}/../tests/lake/examples/test.sh"
    "${LEAN_SOURCE_DIR}/../tests/lake/tests/test.sh"
  )
else()
  file(
    GLOB_RECURSE LEANLAKETESTS
    "${LEAN_SOURCE_DIR}/../tests/lake/examples/test.sh"
    "${LEAN_SOURCE_DIR}/../tests/lake/tests/shake/test.sh"
  )
endif()
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

# Lint test suite and parts of the repository.
# Must not run in parallel with any other tests that may create or delete files.
add_test(NAME lint.py COMMAND python3 lint.py WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}")
set_tests_properties(lint.py PROPERTIES RUN_SERIAL TRUE)

add_test_pile(../doc/examples *.lean)
add_test_pile(compile *.lean BENCH PART2)
add_test_pile(compile_bench *.lean BENCH PART2)
add_test_pile(docparse *.txt)
add_test_pile(
  elab
  *.lean
  EXCEPT
    async_select_channel.lean # Flaky
    sync_mutex.lean # Flaky
)
add_test_pile(elab_bench *.lean BENCH PART2)
add_test_pile(elab_fail *.lean)
add_test_pile(misc *.sh)
add_test_pile(misc_bench *.sh BENCH PART2)
add_test_pile(server *.lean)
add_test_pile(server_interactive *.lean)

add_test_dir(../doc/examples/compiler)
add_test_dir(bench/build BENCH PART1)
add_test_dir(bench/mvcgen/sym BENCH PART2)
add_test_dir(bench/size BENCH PART1)
add_test_dir(lake_bench/inundation BENCH PART2)

add_dir_of_test_dirs(misc_dir)
add_dir_of_test_dirs(
  pkg
  EXCEPT
    signal # Flaky
    test_extern # Flaky
    user_ext # Test started being nondeterministic
)

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

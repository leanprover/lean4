if(REBUILD_STAGE0)
  add_executable(lean_stage0 lean.cpp)
  target_link_libraries(lean_stage0 leanstatic_stage0)
else()
  add_executable(lean_stage0 IMPORTED)
  set_target_properties(lean_stage0 PROPERTIES IMPORTED_LOCATION "${CMAKE_CURRENT_BINARY_DIR}/lean_stage0")
endif()

ADD_CUSTOM_TARGET(bin_lean_stage0
  COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:lean_stage0>" "${LEAN_SOURCE_DIR}/../bin/lean"
  DEPENDS lean_stage0
)

string(TOUPPER "${CMAKE_BUILD_TYPE}" uppercase_CMAKE_BUILD_TYPE)
set(LEANC_OPTS "${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}}")

add_custom_target(make_stdlib
  # '-G Ninja' complains otherwise
  BYPRODUCTS "${CMAKE_BINARY_DIR}/stage1/libleanstdlib.a"
  WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../library"
  COMMAND ${CMAKE_COMMAND} -E env "LEAN_PATH=." make -j8 "${CMAKE_BINARY_DIR}/stage1/libleanstdlib.a" "LEAN=$<TARGET_FILE:lean_stage0>" "LEANC_OPTS=${LEANC_OPTS}" "STAGE1_OUT=${CMAKE_BINARY_DIR}/stage1"
  DEPENDS lean_stage0)
set_target_properties(leanstdlib PROPERTIES
  IMPORTED_LOCATION "${CMAKE_BINARY_DIR}/stage1/libleanstdlib.a"
  IMPORTED_LINK_INTERFACE_LIBRARIES leanstatic)
add_dependencies(leanstdlib make_stdlib)
install(FILES "$<TARGET_FILE:leanstdlib>" DESTINATION lib)

add_custom_target(update-stage0
  COMMAND make update-stage0 "STAGE1_OUT=${CMAKE_BINARY_DIR}/stage1"
  DEPENDS leanstdlib
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/../library")

add_executable(lean lean.cpp)
target_link_libraries(lean leanstatic)
install(TARGETS lean DESTINATION bin)

if(${EMSCRIPTEN})
    set(NODE_JS "node --stack_size=8192")

    file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/lean_with_path
            "#!/bin/sh\nLEAN_PATH=${CMAKE_CURRENT_SOURCE_DIR}/../../library ${NODE_JS} ${CMAKE_CURRENT_BINARY_DIR}/lean.js \"$@\"\n")
    execute_process(COMMAND chmod +x ${CMAKE_CURRENT_BINARY_DIR}/lean_with_path)

    ADD_CUSTOM_TARGET(bin_lean ALL
        COMMAND "${CMAKE_COMMAND}" -E make_directory "${LEAN_SOURCE_DIR}/../bin"
        COMMAND "${CMAKE_COMMAND}" -E copy "${CMAKE_CURRENT_BINARY_DIR}/lean_with_path" "${LEAN_SOURCE_DIR}/../bin/lean"
        DEPENDS lean
        )

    file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/lean
            "#!/bin/sh\n${NODE_JS} ${CMAKE_CURRENT_BINARY_DIR}/lean.js \"$@\"\n")
    execute_process(COMMAND chmod +x ${CMAKE_CURRENT_BINARY_DIR}/lean)

    # legacy code for mkleanbook
    # copy olean files from the library into build/emscripten/shell/library/...
    add_custom_target(lean_js_library
        COMMAND "${CMAKE_COMMAND}" -E remove_directory ${CMAKE_CURRENT_BINARY_DIR}/library
        COMMAND mkdir -p ${CMAKE_CURRENT_BINARY_DIR}/library
        COMMAND bash -c "(cd ${LEAN_JS_LIBRARY}; tar c `find -name '*.olean'`) | (cd ${CMAKE_CURRENT_BINARY_DIR}/library; tar x)"
        VERBATIM)
    file(COPY ${CMAKE_CURRENT_SOURCE_DIR}/lean_js.html DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
    target_link_libraries(lean_js
            "--embed-file library
             --bind
             -s WASM=0
             -s \"BINARYEN_METHOD='native-wasm,asmjs'\"")
    add_dependencies(lean_js lean_js_library)
    set_target_properties(lean_js PROPERTIES COMPILE_FLAGS --bind -s NO_EXIT_RUNTIME=1)

else()
  if (MSVC)
    ADD_CUSTOM_TARGET(bin_lean ALL
      COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:lean>" "$<TARGET_FILE_DIR:lean>/mpir.dll" "${LEAN_SOURCE_DIR}/../bin/"
      DEPENDS lean
    )
  else()
    ADD_CUSTOM_TARGET(bin_lean ALL
      COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:lean>" "${LEAN_SOURCE_DIR}/../bin/"
      DEPENDS lean
    )
  endif()
endif()

# add_test(example1_stdin1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(lean_export ${CMAKE_CURRENT_BINARY_DIR}/lean "-o simple.olean" "${LEAN_SOURCE_DIR}/../tests/lean/run/simple.lean")
add_test(lean_help1    "${CMAKE_CURRENT_BINARY_DIR}/lean" --help)
add_test(lean_help2    "${CMAKE_CURRENT_BINARY_DIR}/lean" -h)
add_test(lean_version1 "${CMAKE_CURRENT_BINARY_DIR}/lean" --version)
if (NOT ${EMSCRIPTEN})
add_test(lean_version2 "${CMAKE_CURRENT_BINARY_DIR}/lean" --v)
endif()
add_test(lean_ghash1   "${CMAKE_CURRENT_BINARY_DIR}/lean" -g)
add_test(lean_ghash2   "${CMAKE_CURRENT_BINARY_DIR}/lean" --githash)
add_test(lean_new_frontend "${LEAN_SOURCE_DIR}/../bin/lean" --new-frontend "${LEAN_SOURCE_DIR}/../library/init/core.lean")
add_test(lean_unknown_option bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "-z")
add_test(lean_unknown_file1 bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "boofoo.lean")
# The following test needs new elaborator to support match
# add_test(NAME "lean_eqn_macro"
#         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#         COMMAND bash "./test_eqn_macro.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
# add_test(NAME "lean_print_notation"
#         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#         COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "print_tests.lean")
# add_test(NAME "issue_597"
#          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#          COMMAND bash "./issue_597.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
# add_test(NAME "issue_616"
#          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#          COMMAND bash "./issue_616.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
# add_test(NAME "show_goal"
#          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#          COMMAND bash "./show_goal.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
# add_test(NAME "issue_755"
#          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#          COMMAND bash "./issue_755.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
# add_test(NAME "print_info"
#          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#          COMMAND bash "./print_info.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
# add_test(NAME "dir_option"
#          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
#          COMMAND "${LEAN_SOURCE_DIR}/../bin/lean" "--dir=${LEAN_SOURCE_DIR}/../library/data/nat" "dir_option.lean")
if (NOT(${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  # The following test cannot be executed on Windows because of the
  # bash script timeout.sh

  # We need to cache failures at type_context to be able to process the following test in a reasonable amount of time
  # add_test(NAME "normalizer_perf"
  #          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
  #          COMMAND bash "./timeout.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "1" "slow1.lean")
endif()

# LEAN TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
FOREACH(T ${LEANTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leantest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
             COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
  endif()
ENDFOREACH(T)

# LEAN RUN TESTS
file(GLOB LEANRUNTESTS "${LEAN_SOURCE_DIR}/../tests/lean/run/*.lean")
FOREACH(T ${LEANRUNTESTS})
  if(NOT T MATCHES "\\.#")
    GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
    add_test(NAME "leanruntest_${T_NAME}"
             WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/run"
             COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
  endif()
ENDFOREACH(T)

# LEAN FAIL TESTS
file(GLOB LEANFAILTESTS "${LEAN_SOURCE_DIR}/../tests/lean/fail/*.lean")
FOREACH(T ${LEANFAILTESTS})
    if(NOT T MATCHES "\\.#")
        GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
        # test twice, once with runner, and once without
        add_test(NAME "leanfailtest_${T_NAME}"
                WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/fail"
                COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
        add_test(NAME "leanfailtest2_${T_NAME}"
                WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/fail"
                COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
    endif()
ENDFOREACH(T)

# LEAN COMPILER TESTS
file(GLOB LEANCOMPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
FOREACH(T ${LEANCOMPTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leancomptest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

# LEAN INTERPRETER TESTS
file(GLOB LEANINTERPTESTS "${LEAN_SOURCE_DIR}/../tests/compiler/*.lean")
FOREACH(T ${LEANINTERPTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leaninterptest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/compiler"
           COMMAND bash "./test_single_interpret.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

# LEAN BENCHMARK TESTS
# do not test all .lean files in bench/
file(GLOB LEANBENCHTESTS "${LEAN_SOURCE_DIR}/../tests/bench/*.lean.expected.out")
FOREACH(T_OUT ${LEANBENCHTESTS})
  string(REPLACE ".expected.out" "" T ${T_OUT})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanbenchtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/bench"
           COMMAND bash "./test_single.sh" ${T_NAME})
ENDFOREACH(T_OUT)

# LEANPKG TESTS
# file(GLOB LEANPKGTESTS "${LEAN_SOURCE_DIR}/../tests/lean/leanpkg/*.sh")
# FOREACH(T ${LEANPKGTESTS})
#   GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
#   if(NOT T_NAME MATCHES "test_single.sh")
#   add_test(NAME "leanpkgtest_${T_NAME}"
#            WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/leanpkg/"
#            COMMAND bash "./test_single.sh" "${LEAN_SOURCE_DIR}/../bin/lean" ${T_NAME})
#   endif()
# ENDFOREACH(T)

# LEAN TESTS using --trust=0
file(GLOB LEANT0TESTS "${LEAN_SOURCE_DIR}/../tests/lean/trust0/*.lean")
FOREACH(T ${LEANT0TESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leant0test_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/trust0"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME} "-t 0")
ENDFOREACH(T)

# LEAN TESTS using --trust=10
file(GLOB LEANT0TESTS "${LEAN_SOURCE_DIR}/../tests/lean/trust10/*.lean")
FOREACH(T ${LEANT0TESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leant10test_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/trust10"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME} "-t 10")
ENDFOREACH(T)

if("${MULTI_THREAD}" MATCHES "ON")
# LEAN INTERACTIVE TESTS
file(GLOB LEANITTESTS "${LEAN_SOURCE_DIR}/../tests/lean/interactive/*.input" "${LEAN_SOURCE_DIR}/../tests/lean/interactive/*.lean")
FOREACH(T ${LEANITTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanittest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/interactive"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)
endif()

# LEAN SLOW TESTS
file(GLOB LEANSLOWTESTS "${LEAN_SOURCE_DIR}/../tests/lean/slow/*.lean")
FOREACH(T ${LEANSLOWTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanslowtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/slow"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
  set_tests_properties("leanslowtest_${T_NAME}" PROPERTIES LABELS "expensive")
ENDFOREACH(T)

# file(GLOB LEANNATIVETESTS "${LEAN_SOURCE_DIR}/../tests/lean/native_run/*.lean")
# FOREACH(T ${LEANNATIVETESTS})
#   GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
#   add_test(NAME "leannativetest_${T_NAME}"
#            WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/native_run"
#            COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
# ENDFOREACH(T)


# # Create the script lean.sh
# # This is used to create a soft dependency on the Lean executable
# # Some rules can only be applied if the lean executable exists,
# # but we don't want a dependency on the executable because
# # the rules would be applied whenever the executable is rebuilt.
# # These are the rules for automatically generating .olean files and
# # C++/Lean interface files.
# add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/lean.sh
#     COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/mk_lean_sh.sh ${CMAKE_CURRENT_BINARY_DIR}
#     DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/lean)
# add_custom_target(lean_sh DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/lean.sh)

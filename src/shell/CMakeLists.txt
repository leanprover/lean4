if(${EMSCRIPTEN})
  add_executable(lean.js lean.cpp emscripten.cpp)
  target_link_libraries(lean.js ${ALL_LIBS} "--embed-file library --memory-init-file 0")
else()
  add_executable(lean lean.cpp emscripten.cpp)
  target_link_libraries(lean ${ALL_LIBS})
  ADD_CUSTOM_COMMAND(TARGET lean
    POST_BUILD
    COMMAND "${CMAKE_COMMAND}" -E make_directory "${LEAN_SOURCE_DIR}/../bin"
    COMMAND "${CMAKE_COMMAND}" -E copy "${CMAKE_CURRENT_BINARY_DIR}/lean${CMAKE_EXECUTABLE_SUFFIX}" "${LEAN_SOURCE_DIR}/../bin/"
    )
  install(TARGETS lean DESTINATION bin)
endif()

add_library(shell emscripten.cpp)
target_link_libraries(shell ${LEAN_LIBS})

# add_test(example1_stdin1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(example1_stdin2 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "-l" "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(example1_stdin3 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "--lean" "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(lean_export ${CMAKE_CURRENT_BINARY_DIR}/lean "-o simple.olean" "${LEAN_SOURCE_DIR}/../tests/lean/run/simple.lean")
add_test(lean_help1    "${CMAKE_CURRENT_BINARY_DIR}/lean" --help)
add_test(lean_help2    "${CMAKE_CURRENT_BINARY_DIR}/lean" -h)
add_test(lean_version1 "${CMAKE_CURRENT_BINARY_DIR}/lean" --version)
add_test(lean_version2 "${CMAKE_CURRENT_BINARY_DIR}/lean" --v)
add_test(lean_ghash1   "${CMAKE_CURRENT_BINARY_DIR}/lean" -g)
add_test(lean_ghash2   "${CMAKE_CURRENT_BINARY_DIR}/lean" --githash)
add_test(lean_path1    "${CMAKE_CURRENT_BINARY_DIR}/lean" -p)
add_test(lean_path2    "${CMAKE_CURRENT_BINARY_DIR}/lean" --path)
add_test(lean_luahook1 "${CMAKE_CURRENT_BINARY_DIR}/lean" --luahook=100 "${LEAN_SOURCE_DIR}/../tests/lua/big.lua")
add_test(lean_luahook2 "${CMAKE_CURRENT_BINARY_DIR}/lean" -k 100 "${LEAN_SOURCE_DIR}/../tests/lua/big.lua")
# add_test(lean_lua1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "--lua" "${LEAN_SOURCE_DIR}/../tests/lua/single.lua")
# add_test(lean_lua2 ${LEAN_SOURCE_DIR}/cmake/redirect.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "-u" "${LEAN_SOURCE_DIR}/../tests/lua/single.lua")
add_test(lean_unknown_option bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "-z")
add_test(lean_unknown_file1 bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "boofoo.lean")
add_test(lean_unknown_file2 bash "${LEAN_SOURCE_DIR}/cmake/check_failure.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "boofoo.lua")
add_test(lean_server_trace "${CMAKE_CURRENT_BINARY_DIR}/lean" --server-trace "${LEAN_SOURCE_DIR}/../tests/lean/interactive/consume_args.input")
add_test(lean_server_trace "${CMAKE_CURRENT_BINARY_DIR}/lean" --server-trace "${LEAN_SOURCE_DIR}/../tests/lean/interactive/options_cmd.trace")
add_test(lean_server_trace "${CMAKE_CURRENT_BINARY_DIR}/lean" --server-trace "${LEAN_SOURCE_DIR}/../tests/lean/interactive/commands.trace")
add_test(NAME "lean_eqn_macro"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
         COMMAND bash "./test_eqn_macro.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
add_test(NAME "lean_print_notation"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
         COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "print_tests.lean")
add_test(NAME "auto_completion_issue_422"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
         COMMAND bash "./ac_bug.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
add_test(NAME "issue_597"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
         COMMAND bash "./issue_597.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
add_test(NAME "issue_616"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
         COMMAND bash "./issue_616.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
add_test(NAME "show_goal"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
         COMMAND bash "./show_goal.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
add_test(NAME "show_goal_bag"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
         COMMAND bash "./show_goal_bag.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
if (NOT(${CMAKE_SYSTEM_NAME} MATCHES "Windows"))
  # The following test cannot be executed on Windows because of the
  # bash script timeout.sh
  add_test(NAME "normalizer_perf"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/extra"
           COMMAND bash "./timeout.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" "1" "slow1.lean")
endif()

# LEAN TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
FOREACH(T ${LEANTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leantest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

# LEAN HoTT TESTS
file(GLOB LEANHTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.hlean")
FOREACH(T ${LEANHTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanhtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

# LEAN RUN TESTS
file(GLOB LEANRUNTESTS "${LEAN_SOURCE_DIR}/../tests/lean/run/*.lean")
FOREACH(T ${LEANRUNTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanruntest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/run"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

# LEAN TESTS using --trust=0
file(GLOB LEANT0TESTS "${LEAN_SOURCE_DIR}/../tests/lean/trust0/*.lean")
FOREACH(T ${LEANT0TESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leant0test_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/trust0"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME} "-t 0")
ENDFOREACH(T)

# LEAN RUN HoTT TESTS
file(GLOB LEANRUNHTESTS "${LEAN_SOURCE_DIR}/../tests/lean/hott/*.hlean")
FOREACH(T ${LEANRUNHTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanhotttest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/hott"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

if("${MULTI_THREAD}" MATCHES "ON")
# LEAN INTERACTIVE TESTS
file(GLOB LEANITTESTS "${LEAN_SOURCE_DIR}/../tests/lean/interactive/*.input")
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

# LEAN LUA TESTS
file(GLOB LEANLUATESTS "${LEAN_SOURCE_DIR}/../tests/lua/*.lua")
FOREACH(T ${LEANLUATESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluatest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

# LEAN LUA SLOW TESTS
file(GLOB LEANLUASLOWTESTS "${LEAN_SOURCE_DIR}/../tests/lua/slow/*.lua")
FOREACH(T ${LEANLUASLOWTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluaslowtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua/slow"
           COMMAND bash "../test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
  set_tests_properties("leanluaslowtest_${T_NAME}" PROPERTIES LABELS "expensive")
ENDFOREACH(T)

# LEAN DOCS
file(GLOB LEANDOCS "${LEAN_SOURCE_DIR}/../doc/lean/*.org")
FOREACH(T ${LEANDOCS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leandoc_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/lean"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

# LEAN LUA DOCS
file(GLOB LEANLUADOCS "${LEAN_SOURCE_DIR}/../doc/lua/*.md")
FOREACH(T ${LEANLUADOCS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluadoc_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/lua"
           COMMAND bash "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

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

add_executable(lean lean.cpp)
target_link_libraries(lean ${EXTRA_LIBS})

install(TARGETS lean DESTINATION bin)

# add_test(example1_stdin1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(example1_stdin2 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "-l" "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(example1_stdin3 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "--lean" "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
# add_test(lean_export ${CMAKE_CURRENT_BINARY_DIR}/lean "-o simple.olean" "${LEAN_SOURCE_DIR}/../tests/lean/run/simple.lean")
add_test(lean_help1 ${CMAKE_CURRENT_BINARY_DIR}/lean --help)
add_test(lean_help2 ${CMAKE_CURRENT_BINARY_DIR}/lean --h)
add_test(lean_version1 ${CMAKE_CURRENT_BINARY_DIR}/lean --version)
add_test(lean_version2 ${CMAKE_CURRENT_BINARY_DIR}/lean --v)
add_test(lean_ghash1 ${CMAKE_CURRENT_BINARY_DIR}/lean -g)
add_test(lean_ghash2 ${CMAKE_CURRENT_BINARY_DIR}/lean --githash)
add_test(lean_path1 ${CMAKE_CURRENT_BINARY_DIR}/lean -p)
add_test(lean_path2 ${CMAKE_CURRENT_BINARY_DIR}/lean --path)
add_test(lean_luahook1 ${CMAKE_CURRENT_BINARY_DIR}/lean --luahook=100 "${LEAN_SOURCE_DIR}/../tests/lua/big.lua")
add_test(lean_luahook2 ${CMAKE_CURRENT_BINARY_DIR}/lean -c 100 "${LEAN_SOURCE_DIR}/../tests/lua/big.lua")
# add_test(lean_lua1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "--lua" "${LEAN_SOURCE_DIR}/../tests/lua/single.lua")
# add_test(lean_lua2 ${LEAN_SOURCE_DIR}/cmake/redirect.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "-u" "${LEAN_SOURCE_DIR}/../tests/lua/single.lua")
add_test(lean_unknown_option ${LEAN_SOURCE_DIR}/cmake/check_failure.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "-z")
add_test(lean_unknown_file1 ${LEAN_SOURCE_DIR}/cmake/check_failure.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "boofoo.lean")
add_test(lean_unknown_file2 ${LEAN_SOURCE_DIR}/cmake/check_failure.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "boofoo.lua")

# # LEAN EXAMPLES
# file(GLOB LEANEXAMPLES "${LEAN_SOURCE_DIR}/../examples/lean/*.lean")
# FOREACH(T ${LEANEXAMPLES})
#   GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
#   add_test(NAME "leanex_${T_NAME}"
#     COMMAND ${CMAKE_CURRENT_BINARY_DIR}/lean ${T})
# ENDFOREACH(T)

# LEAN TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
FOREACH(T ${LEANTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leantest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean -t 100000" ${T_NAME})
ENDFOREACH(T)

# LEAN RUN TESTS
file(GLOB LEANRUNTESTS "${LEAN_SOURCE_DIR}/../tests/lean/run/*.lean")
FOREACH(T ${LEANRUNTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanruntest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/run"
           COMMAND "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T_NAME})
ENDFOREACH(T)

# # LEAN SLOW TESTS
# file(GLOB LEANSLOWTESTS "${LEAN_SOURCE_DIR}/../tests/lean/slow/*.lean")
# FOREACH(T ${LEANSLOWTESTS})
#   GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
#   add_test(NAME "leanslowtest_${T_NAME}"
#            WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/slow"
#            COMMAND "../test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean -t" ${T_NAME})
# ENDFOREACH(T)

# LEAN LUA TESTS
file(GLOB LEANLUATESTS "${LEAN_SOURCE_DIR}/../tests/lua/*.lua")
FOREACH(T ${LEANLUATESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluatest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean -t 100000" ${T_NAME})
ENDFOREACH(T)

# LEAN LUA SLOW TESTS
file(GLOB LEANLUASLOWTESTS "${LEAN_SOURCE_DIR}/../tests/lua/slow/*.lua")
FOREACH(T ${LEANLUASLOWTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluaslowtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua/slow"
           COMMAND "../test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean -t 100000" ${T_NAME})
  set_tests_properties("leanluaslowtest_${T_NAME}" PROPERTIES LABELS "expensive")
ENDFOREACH(T)

# # LEAN DOCS
# file(GLOB LEANDOCS "${LEAN_SOURCE_DIR}/../doc/lean/*.md")
# FOREACH(T ${LEANDOCS})
#   GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
#   add_test(NAME "leandoc_${T_NAME}"
#            WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/lean"
#            COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean -t" ${T})
# ENDFOREACH(T)

# LEAN LUA DOCS
file(GLOB LEANLUADOCS "${LEAN_SOURCE_DIR}/../doc/lua/*.md")
FOREACH(T ${LEANLUADOCS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluadoc_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/lua"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean -t 100000" ${T})
ENDFOREACH(T)

# LEAN LUA THREAD TESTS
if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Linux"))
  if ((NOT (${CMAKE_CXX_COMPILER} MATCHES "clang")) AND (${MULTI_THREAD} MATCHES "ON"))
    file(GLOB LEANLUATHREADTESTS "${LEAN_SOURCE_DIR}/../tests/lua/threads/*.lua")
    FOREACH(T ${LEANLUATHREADTESTS})
      GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
      add_test(NAME "leanluathreadtest_${T_NAME}"
        WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua/threads"
        COMMAND "../test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean -t 100000" ${T})
    ENDFOREACH(T)
  endif()
endif()

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

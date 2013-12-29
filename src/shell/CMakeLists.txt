# In our build, githash.h should not depend on .git/index.
# The problem is that we store automatically generated files in the repository because we want to support cross-compilation.
# Soonho and Leo also use custom shell prompts that invoke git to produce visual cues when files were modified.
# So, the following vicious cycle may happen if we use .git/index.
#   1- Build lean, then automatically generated files are created.
#   2- If we do anything in the shell (even pressing RETURN), the custom shell prompt invokes git, that checks for changes.
#   3- Even if the automatically generated files are not modified, the .git/index date changes.
#   4- If we try to build again, the builds detects that .git/index date changed, and generates githash.h again
#   5- Then, lean executable is built again
#   6- Then, automatically generated files are created again using the lean executable.
#   7- Cycle continues at step 2.
# To avoid this cycle, we are using .git/COMMIT_EDITMSG and .git/FETCH_HEAD as the actual dependencies for githash.h
# It is not clear whether this really fixes the problem or not.
set(GITHASH_DEPS ${LEAN_SOURCE_DIR}/../.git/COMMIT_EDITMSG ${LEAN_SOURCE_DIR}/../.git/FETCH_HEAD)
add_custom_command(
  OUTPUT ${LEAN_BINARY_DIR}/githash.h
  COMMAND ${LEAN_SOURCE_DIR}/cmake/mk_githash_dot_h.sh ${LEAN_BINARY_DIR}
  DEPENDS ${GITHASH_DEPS}
)
add_custom_target(githash
  DEPENDS ${LEAN_BINARY_DIR}/githash.h ${GITHASH_DEPS}
)

add_executable(lean lean.cpp)
add_dependencies(lean githash)
target_link_libraries(lean ${EXTRA_LIBS})

install(TARGETS lean DESTINATION bin)

add_test(example1_stdin1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
add_test(example1_stdin2 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "-l" "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
add_test(example1_stdin3 ${LEAN_SOURCE_DIR}/cmake/redirect.sh ${CMAKE_CURRENT_BINARY_DIR}/lean "--lean" "${LEAN_SOURCE_DIR}/../tests/lean/single.lean")
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
add_test(lean_lua1 ${LEAN_SOURCE_DIR}/cmake/redirect.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "--lua" "${LEAN_SOURCE_DIR}/../tests/lua/single.lua")
add_test(lean_lua2 ${LEAN_SOURCE_DIR}/cmake/redirect.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "-u" "${LEAN_SOURCE_DIR}/../tests/lua/single.lua")
add_test(lean_unknown_option ${LEAN_SOURCE_DIR}/cmake/check_failure.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "-z")
add_test(lean_unknown_file1 ${LEAN_SOURCE_DIR}/cmake/check_failure.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "boofoo.lean")
add_test(lean_unknown_file2 ${LEAN_SOURCE_DIR}/cmake/check_failure.sh "${CMAKE_CURRENT_BINARY_DIR}/lean" "boofoo.lua")

# LEAN EXAMPLES
file(GLOB LEANEXAMPLES "${LEAN_SOURCE_DIR}/../examples/lean/*.lean")
FOREACH(T ${LEANEXAMPLES})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanex_${T_NAME}"
    COMMAND ${CMAKE_CURRENT_BINARY_DIR}/lean ${T})
ENDFOREACH(T)

# LEAN TESTS
file(GLOB LEANTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
FOREACH(T ${LEANTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leantest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

# LEAN PP TESTS
# For making sure that Lean can parse the output produced by its pretty printer
file(GLOB LEANPPTESTS "${LEAN_SOURCE_DIR}/../tests/lean/*.lean")
FOREACH(T ${LEANPPTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanpptest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
           COMMAND "./test_single_pp.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

# LEAN INTERACTIVE TESTS
file(GLOB LEANINTERACTIVETESTS "${LEAN_SOURCE_DIR}/../tests/lean/interactive/*.lean")
FOREACH(T ${LEANINTERACTIVETESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leaninteractivetest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/interactive"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

# LEAN SLOW TESTS
file(GLOB LEANSLOWTESTS "${LEAN_SOURCE_DIR}/../tests/lean/slow/*.lean")
FOREACH(T ${LEANSLOWTESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanslowtest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/slow"
           COMMAND "../test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

# LEAN LUA TESTS
file(GLOB LEANLUATESTS "${LEAN_SOURCE_DIR}/../tests/lua/*.lua")
FOREACH(T ${LEANLUATESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluatest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

# LEAN LUA DOCS
file(GLOB LEANLUADOCS "${LEAN_SOURCE_DIR}/../doc/lua/*.md")
FOREACH(T ${LEANLUADOCS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluadoc_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/lua"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
ENDFOREACH(T)

# LEAN LUA THREAD TESTS
if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Linux"))
  if ((NOT (${CMAKE_CXX_COMPILER} MATCHES "clang")) AND (${MULTI_THREAD} MATCHES "ON"))
    file(GLOB LEANLUATHREADTESTS "${LEAN_SOURCE_DIR}/../tests/lua/threads/*.lua")
    FOREACH(T ${LEANLUATHREADTESTS})
      GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
      add_test(NAME "leanluathreadtest_${T_NAME}"
        WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua/threads"
        COMMAND "../test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
    ENDFOREACH(T)
  endif()
endif()

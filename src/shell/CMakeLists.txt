configure_file("${LEAN_SOURCE_DIR}/shell/version.h.in" "${LEAN_BINARY_DIR}/version.h")
include_directories("${LEAN_BINARY_DIR}")
add_executable(lean lean.cpp)
add_dependencies(lean githash)
target_link_libraries(lean ${EXTRA_LIBS})

add_test(example1_stdin ${CMAKE_CURRENT_BINARY_DIR}/lean < "${LEAN_SOURCE_DIR}/../examples/lean/ex1.lean")

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
  if ((NOT (${CMAKE_CXX_COMPILER} MATCHES "clang")) AND (${THREAD_SAFE} MATCHES "ON"))
    file(GLOB LEANLUATHREADTESTS "${LEAN_SOURCE_DIR}/../tests/lua/threads/*.lua")
    FOREACH(T ${LEANLUATHREADTESTS})
      GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
      add_test(NAME "leanluathreadtest_${T_NAME}"
        WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua/threads"
        COMMAND "../test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean" ${T})
    ENDFOREACH(T)
  endif()
endif()

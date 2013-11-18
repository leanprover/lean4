add_executable(leanlua leanlua.cpp)
target_link_libraries(leanlua ${EXTRA_LIBS})

# LEANLUATESTS
file(GLOB LEANLUATESTS "${LEAN_SOURCE_DIR}/../tests/lua/*.lua")
FOREACH(T ${LEANLUATESTS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluatest_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/leanlua" ${T})
ENDFOREACH(T)

# LEANLUADOCS
file(GLOB LEANLUADOCS "${LEAN_SOURCE_DIR}/../doc/lua/*.md")
FOREACH(T ${LEANLUADOCS})
  GET_FILENAME_COMPONENT(T_NAME ${T} NAME)
  add_test(NAME "leanluadoc_${T_NAME}"
           WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/lua"
           COMMAND "./test_single.sh" "${CMAKE_CURRENT_BINARY_DIR}/leanlua" ${T})
ENDFOREACH(T)

if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Linux"))
  if (NOT (${CMAKE_CXX_COMPILER} MATCHES "clang"))
    add_test(NAME leanluathreadtests
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua/threads"
      COMMAND "../test.sh" "${CMAKE_CURRENT_BINARY_DIR}/leanlua")
  endif()
endif()

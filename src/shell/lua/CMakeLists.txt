add_executable(leanlua leanlua.cpp)
target_link_libraries(leanlua ${EXTRA_LIBS})
add_test(NAME leanluatests
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua"
         COMMAND "./test.sh" "${CMAKE_CURRENT_BINARY_DIR}/leanlua")

add_test(NAME leanluadocs
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../doc/lua"
         COMMAND "./test.sh" "${CMAKE_CURRENT_BINARY_DIR}/leanlua")

if((${CYGWIN} EQUAL "1") OR (${CMAKE_SYSTEM_NAME} MATCHES "Linux"))
  if (NOT (${CMAKE_CXX_COMPILER} MATCHES "clang"))
    add_test(NAME leanluathreadtests
      WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua/threads"
      COMMAND "../test.sh" "${CMAKE_CURRENT_BINARY_DIR}/leanlua")
  endif()
endif()

add_executable(leanlua leanlua.cpp)
target_link_libraries(leanlua ${EXTRA_LIBS})
add_test(NAME leanluatests
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lua"
         COMMAND "./test.sh" "${CMAKE_CURRENT_BINARY_DIR}/leanlua")

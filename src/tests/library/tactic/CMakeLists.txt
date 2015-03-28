add_executable(tactic_tst tactic.cpp)
target_link_libraries(tactic_tst ${EXTRA_LIBS})
add_test(tactic "${CMAKE_CURRENT_BINARY_DIR}/tactic_tst")
set_tests_properties(tactic PROPERTIES ENVIRONMENT "LEAN_PATH=${LEAN_BINARY_DIR}/shell")

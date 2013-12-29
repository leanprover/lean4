add_executable(elaborator_tst elaborator.cpp)
target_link_libraries(elaborator_tst ${EXTRA_LIBS})
add_test(elaborator_tst ${CMAKE_CURRENT_BINARY_DIR}/elaborator_tst)
set_tests_properties(elaborator_tst PROPERTIES ENVIRONMENT "LEAN_PATH=${LEAN_BINARY_DIR}/shell")

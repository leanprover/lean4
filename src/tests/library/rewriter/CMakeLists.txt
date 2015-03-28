add_executable(rewriter_tst rewriter.cpp)
target_link_libraries(rewriter_tst ${EXTRA_LIBS})
add_test(rewriter_tst "${CMAKE_CURRENT_BINARY_DIR}/rewriter_tst")
set_tests_properties(rewriter_tst PROPERTIES ENVIRONMENT "LEAN_PATH=${LEAN_BINARY_DIR}/shell")

add_executable(fo_match_tst fo_match.cpp)
target_link_libraries(fo_match_tst ${EXTRA_LIBS})
add_test(fo_match_tst "${CMAKE_CURRENT_BINARY_DIR}/fo_match_tst")

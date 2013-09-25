add_executable(rewriter_tst rewriter.cpp)
target_link_libraries(rewriter_tst ${EXTRA_LIBS})
add_test(rewriter ${CMAKE_CURRENT_BINARY_DIR}/rewriter_tst)

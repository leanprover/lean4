add_executable(rewrite_tst rewrite.cpp)
target_link_libraries(rewrite_tst ${EXTRA_LIBS})
add_test(rewrite ${CMAKE_CURRENT_BINARY_DIR}/rewrite_tst)

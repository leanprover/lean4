add_executable(expr_tst expr.cpp)
target_link_libraries(expr_tst ${EXTRA_LIBS})
add_test(expr ${CMAKE_CURRENT_BINARY_DIR}/expr_tst)

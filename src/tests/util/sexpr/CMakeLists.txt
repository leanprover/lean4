add_executable(sexpr_tst sexpr.cpp)
target_link_libraries(sexpr_tst ${EXTRA_LIBS})
add_test(sexpr ${CMAKE_CURRENT_BINARY_DIR}/sexpr_tst)

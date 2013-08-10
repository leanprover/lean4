add_executable(frontend_tst frontend.cpp)
target_link_libraries(frontend_tst ${EXTRA_LIBS})
add_test(frontend ${CMAKE_CURRENT_BINARY_DIR}/frontend_tst)

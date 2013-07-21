add_executable(interval_tst interval.cpp)
target_link_libraries(interval_tst ${EXTRA_LIBS})
add_test(interval ${CMAKE_CURRENT_BINARY_DIR}/interval_tst)

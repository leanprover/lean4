add_executable(test_interval interval.cpp)
target_link_libraries(test_interval ${EXTRA_LIBS})
add_test(interval ${CMAKE_CURRENT_BINARY_DIR}/test_interval)

add_executable(shared_test shared.cpp)
target_link_libraries(shared_test ${EXTRA_LIBS} leanshared)
add_test(shared_test "${CMAKE_CURRENT_BINARY_DIR}/shared_test")

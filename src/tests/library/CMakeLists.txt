add_executable(light_checker light_checker.cpp)
target_link_libraries(light_checker ${EXTRA_LIBS})
add_test(light_checker ${CMAKE_CURRENT_BINARY_DIR}/light_checker)

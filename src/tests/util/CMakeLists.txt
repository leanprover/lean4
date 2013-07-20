add_executable(interrupt interrupt.cpp)
target_link_libraries(interrupt ${EXTRA_LIBS})
add_test(interrupt ${CMAKE_CURRENT_BINARY_DIR}/interrupt)

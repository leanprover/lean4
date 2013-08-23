add_executable(beta beta.cpp)
target_link_libraries(beta ${EXTRA_LIBS})
add_test(beta ${CMAKE_CURRENT_BINARY_DIR}/beta)

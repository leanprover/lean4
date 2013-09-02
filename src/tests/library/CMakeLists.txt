add_executable(metavar metavar.cpp)
target_link_libraries(metavar ${EXTRA_LIBS})
add_test(metavar ${CMAKE_CURRENT_BINARY_DIR}/metavar)

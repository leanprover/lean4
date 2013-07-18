add_executable(mpq mpq.cpp)
target_link_libraries(mpq ${EXTRA_LIBS})
add_test(mpq ${CMAKE_CURRENT_BINARY_DIR}/mpq)

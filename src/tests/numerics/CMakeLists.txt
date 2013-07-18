include_directories(${LEAN_SOURCE_DIR}/numerics) 
add_executable(mpq mpq.cpp)
add_test(mpq ${CMAKE_CURRENT_BINARY_DIR}/mpq)
target_link_libraries(mpq ${EXTRA_LIBS})

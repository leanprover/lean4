add_executable(union_find union_find.cpp)
target_link_libraries(union_find "util" ${EXTRA_LIBS})
add_test(union_find "${CMAKE_CURRENT_BINARY_DIR}/union_find")

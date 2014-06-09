add_library(lean_frontend register_module.cpp token_set.cpp
scanner.cpp parse_table.cpp)

target_link_libraries(lean_frontend ${LEAN_LIBS})

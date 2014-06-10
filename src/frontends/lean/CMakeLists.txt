add_library(lean_frontend register_module.cpp token_table.cpp
scanner.cpp parse_table.cpp parser_config.cpp)

target_link_libraries(lean_frontend ${LEAN_LIBS})

add_library(lean_frontend lean_frontend.cpp lean_operator_info.cpp lean_scanner.cpp lean_parser.cpp lean_pp.cpp lean_notation.cpp)
target_link_libraries(lean_frontend ${LEAN_LIBS})

add_library(frontend frontend.cpp operator_info.cpp scanner.cpp parser.cpp pp.cpp builtin_notation.cpp)
target_link_libraries(frontend ${LEAN_LIBS})

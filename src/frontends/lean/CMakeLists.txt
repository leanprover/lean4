add_library(lean_frontend frontend.cpp operator_info.cpp scanner.cpp parser.cpp pp.cpp
  notation.cpp elaborator.cpp elaborator_exception.cpp)
target_link_libraries(lean_frontend ${LEAN_LIBS})

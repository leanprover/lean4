add_library(lean_frontend frontend.cpp operator_info.cpp scanner.cpp parser.cpp pp.cpp
  notation.cpp frontend_elaborator.cpp register_module.cpp environment_scope.cpp)
target_link_libraries(lean_frontend ${LEAN_LIBS})

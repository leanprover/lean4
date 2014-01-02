add_library(lean_frontend frontend.cpp operator_info.cpp scanner.cpp
  parser.cpp parser_imp.cpp parser_expr.cpp parser_error.cpp
  parser_imp.cpp parser_cmds.cpp parser_level.cpp parser_tactic.cpp
  parser_macros.cpp parser_calc.cpp pp.cpp frontend_elaborator.cpp
  register_module.cpp environment_scope.cpp coercion.cpp shell.cpp)

target_link_libraries(lean_frontend ${LEAN_LIBS})

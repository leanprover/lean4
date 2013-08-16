add_library(kernel expr.cpp free_vars.cpp abstract.cpp instantiate.cpp
  normalize.cpp context.cpp level.cpp object.cpp environment.cpp
  type_check.cpp builtin.cpp expr_formatter.cpp occurs.cpp)

target_link_libraries(kernel ${LEAN_LIBS})

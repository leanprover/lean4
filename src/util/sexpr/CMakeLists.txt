add_library(sexpr sexpr.cpp sexpr_fn.cpp format.cpp options.cpp
  option_declarations.cpp init_module.cpp)

target_link_libraries(sexpr ${LEAN_LIBS})

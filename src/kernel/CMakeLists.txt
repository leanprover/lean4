add_library(kernel expr.cpp free_vars.cpp abstract.cpp instantiate.cpp
  normalizer.cpp context.cpp level.cpp object.cpp environment.cpp
  type_checker.cpp builtin.cpp occurs.cpp metavar.cpp justification.cpp
  unification_constraint.cpp printer.cpp formatter.cpp has_cached_type.cpp
  kernel_exception.cpp type_checker_justification.cpp pos_info_provider.cpp
  replace_visitor.cpp)

target_link_libraries(kernel ${LEAN_LIBS})

add_library(blast OBJECT expr.cpp state.cpp blast.cpp blast_tactic.cpp
  init_module.cpp proof_expr.cpp options.cpp choice_point.cpp
  simple_strategy.cpp util.cpp gexpr.cpp revert.cpp strategy.cpp
  congruence_closure.cpp trace.cpp imp_extension.cpp)

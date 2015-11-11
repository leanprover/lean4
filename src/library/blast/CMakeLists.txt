add_library(blast OBJECT expr.cpp state.cpp blast.cpp blast_tactic.cpp
  init_module.cpp simplifier.cpp assumption.cpp intros.cpp proof_expr.cpp
  options.cpp choice_point.cpp simple_strategy.cpp backward.cpp)

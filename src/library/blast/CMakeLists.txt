add_library(blast OBJECT expr.cpp state.cpp blast.cpp blast_tactic.cpp
  init_module.cpp simplifier.cpp simple_actions.cpp intros_action.cpp proof_expr.cpp
  options.cpp choice_point.cpp simple_strategy.cpp util.cpp
  gexpr.cpp revert.cpp subst_action.cpp no_confusion_action.cpp
  simplify_actions.cpp strategy.cpp recursor_action.cpp congruence_closure.cpp
  trace.cpp)

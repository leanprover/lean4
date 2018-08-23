add_library(tactic OBJECT occurrences.cpp kabstract.cpp tactic_state.cpp
  intro_tactic.cpp revert_tactic.cpp clear_tactic.cpp
  app_builder_tactics.cpp subst_tactic.cpp exact_tactic.cpp
  change_tactic.cpp assert_tactic.cpp
  fun_info_tactics.cpp induction_tactic.cpp cases_tactic.cpp
  generalize_tactic.cpp hsubstitution.cpp gexpr.cpp elaborate.cpp init_module.cpp
  eval.cpp destruct_tactic.cpp elaborator_exception.cpp tactic_evaluator.cpp)

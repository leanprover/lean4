add_library(tactic OBJECT occurrences.cpp kabstract.cpp tactic_state.cpp
  intro_tactic.cpp revert_tactic.cpp clear_tactic.cpp
  subst_tactic.cpp exact_tactic.cpp
  induction_tactic.cpp cases_tactic.cpp
  hsubstitution.cpp gexpr.cpp elaborate.cpp init_module.cpp
  eval.cpp elaborator_exception.cpp tactic_evaluator.cpp)

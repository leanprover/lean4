add_library(tactic OBJECT tactic_state.cpp intro_tactic.cpp
  revert_tactic.cpp rename_tactic.cpp clear_tactic.cpp
  app_builder_tactics.cpp subst_tactic.cpp exact_tactic.cpp
  change_tactic.cpp assert_tactic.cpp apply_tactic.cpp
  fun_info_tactics.cpp congr_lemma_tactics.cpp abstract_expr_tactics.cpp
  elaborate.cpp init_module.cpp)

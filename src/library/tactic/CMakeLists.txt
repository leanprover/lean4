add_library(tactic OBJECT tactic_state.cpp intro_tactic.cpp assumption_tactic.cpp
  revert_tactic.cpp rename_tactic.cpp clear_tactic.cpp
  app_builder_tactics.cpp elaborate.cpp init_module.cpp)

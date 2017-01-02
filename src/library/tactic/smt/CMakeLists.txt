add_library(smt OBJECT congruence_closure.cpp congruence_tactics.cpp
  hinst_lemmas.cpp ematch.cpp theory_ac.cpp util.cpp
  unit_propagation.cpp smt_state.cpp init_module.cpp)

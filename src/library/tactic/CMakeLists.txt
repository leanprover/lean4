add_library(tactic goal.cpp proof_state.cpp tactic.cpp elaborate.cpp
apply_tactic.cpp intros_tactic.cpp rename_tactic.cpp trace_tactic.cpp
exact_tactic.cpp generalize_tactic.cpp inversion_tactic.cpp
whnf_tactic.cpp revert_tactic.cpp assert_tactic.cpp clear_tactic.cpp
expr_to_tactic.cpp location.cpp rewrite_tactic.cpp util.cpp
init_module.cpp change_tactic.cpp check_expr_tactic.cpp let_tactic.cpp
contradiction_tactic.cpp exfalso_tactic.cpp constructor_tactic.cpp
injection_tactic.cpp congruence_tactic.cpp relation_tactics.cpp
induction_tactic.cpp subst_tactic.cpp unfold_rec.cpp with_options_tactic.cpp)

target_link_libraries(tactic ${LEAN_LIBS})

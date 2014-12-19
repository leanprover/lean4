add_library(tactic goal.cpp proof_state.cpp tactic.cpp elaborate.cpp
apply_tactic.cpp intros_tactic.cpp rename_tactic.cpp trace_tactic.cpp
exact_tactic.cpp unfold_tactic.cpp generalize_tactic.cpp
inversion_tactic.cpp whnf_tactic.cpp revert_tactic.cpp
assert_tactic.cpp clear_tactic.cpp expr_to_tactic.cpp util.cpp
placeholder_elaborator.cpp init_module.cpp)

target_link_libraries(tactic ${LEAN_LIBS})

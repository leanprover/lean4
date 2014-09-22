add_library(tactic goal.cpp proof_state.cpp tactic.cpp apply_tactic.cpp
expr_to_tactic.cpp init_module.cpp)

# simplify_tactic.cpp)

target_link_libraries(tactic ${LEAN_LIBS})

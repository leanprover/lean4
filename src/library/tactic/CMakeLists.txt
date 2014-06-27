add_library(tactic goal.cpp cex_builder.cpp proof_builder.cpp proof_state.cpp)

# tactic.cpp apply_tactic.cpp
# simplify_tactic.cpp)

target_link_libraries(tactic ${LEAN_LIBS})

add_library(tactic goal.cpp proof_builder.cpp cex_builder.cpp
proof_state.cpp tactic.cpp boolean.cpp)

target_link_libraries(tactic ${LEAN_LIBS})

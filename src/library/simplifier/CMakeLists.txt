add_library(simplifier ceqv.cpp simp_rule_set.cpp init_module.cpp simp_tactic.cpp)
target_link_libraries(simplifier ${LEAN_LIBS})

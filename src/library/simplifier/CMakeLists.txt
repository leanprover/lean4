add_library(simplifier ceq.cpp simplifier.cpp rewrite_rule_set.cpp)
target_link_libraries(simplifier ${LEAN_LIBS})

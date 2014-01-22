add_library(simplifier ceq.cpp congr.cpp rewrite_rule_set.cpp simplifier.cpp)
target_link_libraries(simplifier ${LEAN_LIBS})

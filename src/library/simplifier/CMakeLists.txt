add_library(simplifier ceqv.cpp rewrite_rule_set.cpp init_module.cpp)
target_link_libraries(simplifier ${LEAN_LIBS})

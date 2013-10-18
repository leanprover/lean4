add_library(library basic_thms.cpp deep_copy.cpp max_sharing.cpp
  context_to_lambda.cpp state.cpp update_expr.cpp reduce.cpp
  type_inferer.cpp placeholder.cpp ho_unifier.cpp expr_lt.cpp)

target_link_libraries(library ${LEAN_LIBS})

add_library(library basic_thms.cpp deep_copy.cpp max_sharing.cpp
  context_to_lambda.cpp io_state.cpp update_expr.cpp type_inferer.cpp
  placeholder.cpp expr_lt.cpp script_evaluator.cpp)

target_link_libraries(library ${LEAN_LIBS})

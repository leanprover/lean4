add_library(library basic_thms.cpp deep_copy.cpp max_sharing.cpp
  printer.cpp formatter.cpp context_to_lambda.cpp
  state.cpp metavar.cpp update_expr.cpp kernel_exception_formatter.cpp
  reduce.cpp light_checker.cpp)
target_link_libraries(library ${LEAN_LIBS})

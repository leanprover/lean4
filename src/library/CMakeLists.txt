add_library(library kernel_bindings.cpp deep_copy.cpp
  context_to_lambda.cpp placeholder.cpp expr_lt.cpp substitution.cpp
  fo_unify.cpp bin_op.cpp equality.cpp io_state_stream.cpp printer.cpp
  hop_match.cpp ite.cpp heq_decls.cpp cast_decls.cpp)

target_link_libraries(library ${LEAN_LIBS})

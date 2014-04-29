add_library(library deep_copy.cpp expr_lt.cpp io_state.cpp
  occurs.cpp kernel_bindings.cpp io_state_stream.cpp)
# context_to_lambda.cpp placeholder.cpp
# fo_unify.cpp bin_op.cpp equality.cpp
# hop_match.cpp)

target_link_libraries(library ${LEAN_LIBS})

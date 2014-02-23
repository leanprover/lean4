add_library(library deep_copy.cpp expr_lt.cpp io_state_stream.cpp)
# kernel_bindings.cpp
# context_to_lambda.cpp placeholder.cpp
# fo_unify.cpp bin_op.cpp equality.cpp
# hop_match.cpp)

target_link_libraries(library ${LEAN_LIBS})

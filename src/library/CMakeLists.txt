add_library(library kernel_bindings.cpp basic_thms.cpp deep_copy.cpp
  max_sharing.cpp context_to_lambda.cpp io_state.cpp type_inferer.cpp
  placeholder.cpp expr_lt.cpp substitution.cpp
  fo_unify.cpp)

target_link_libraries(library ${LEAN_LIBS})

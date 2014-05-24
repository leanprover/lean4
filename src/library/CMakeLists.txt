add_library(library deep_copy.cpp expr_lt.cpp io_state.cpp occurs.cpp
  kernel_bindings.cpp io_state_stream.cpp bin_app.cpp
  resolve_macro.cpp kernel_serializer.cpp max_sharing.cpp
  normalize.cpp shared_environment.cpp module.cpp coercion.cpp)
# placeholder.cpp fo_unify.cpp hop_match.cpp)

target_link_libraries(library ${LEAN_LIBS})

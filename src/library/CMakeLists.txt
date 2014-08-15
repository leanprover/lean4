add_library(library deep_copy.cpp expr_lt.cpp io_state.cpp occurs.cpp
  kernel_bindings.cpp io_state_stream.cpp bin_app.cpp
  resolve_macro.cpp kernel_serializer.cpp max_sharing.cpp
  normalize.cpp shared_environment.cpp module.cpp coercion.cpp
  private.cpp placeholder.cpp aliases.cpp level_names.cpp
  update_declaration.cpp choice.cpp scoped_ext.cpp locals.cpp
  standard_kernel.cpp hott_kernel.cpp
  unifier.cpp unifier_plugin.cpp inductive_unifier_plugin.cpp
  explicit.cpp num.cpp string.cpp opaque_hints.cpp head_map.cpp
  match.cpp definitions_cache.cpp declaration_index.cpp)

target_link_libraries(library ${LEAN_LIBS})

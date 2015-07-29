add_library(library deep_copy.cpp expr_lt.cpp io_state.cpp occurs.cpp
  kernel_bindings.cpp io_state_stream.cpp bin_app.cpp constants.cpp
  resolve_macro.cpp kernel_serializer.cpp max_sharing.cpp
  normalize.cpp shared_environment.cpp module.cpp coercion.cpp
  private.cpp placeholder.cpp aliases.cpp level_names.cpp
  update_declaration.cpp choice.cpp scoped_ext.cpp locals.cpp
  standard_kernel.cpp sorry.cpp replace_visitor.cpp unifier.cpp
  unifier_plugin.cpp inductive_unifier_plugin.cpp explicit.cpp num.cpp
  string.cpp head_map.cpp match.cpp definition_cache.cpp
  declaration_index.cpp class.cpp util.cpp print.cpp annotation.cpp
  typed_expr.cpp let.cpp type_util.cpp protected.cpp
  metavar_closure.cpp reducible.cpp init_module.cpp
  generic_exception.cpp fingerprint.cpp flycheck.cpp hott_kernel.cpp
  local_context.cpp choice_iterator.cpp pp_options.cpp
  unfold_macros.cpp app_builder.cpp projection.cpp abbreviation.cpp
  relation_manager.cpp export.cpp user_recursors.cpp
  class_instance_synth.cpp idx_metavar.cpp composition_manager.cpp
  tc_multigraph.cpp noncomputable.cpp)

target_link_libraries(library ${LEAN_LIBS})

add_library(library OBJECT deep_copy.cpp expr_lt.cpp io_state.cpp
  io_state_stream.cpp bin_app.cpp constants.cpp kernel_serializer.cpp
  max_sharing.cpp shared_environment.cpp module.cpp
  private.cpp placeholder.cpp aliases.cpp level_names.cpp
  update_declaration.cpp scoped_ext.cpp standard_kernel.cpp sorry.cpp replace_visitor.cpp
  explicit.cpp num.cpp string.cpp head_map.cpp definition_cache.cpp
  declaration_index.cpp class.cpp util.cpp print.cpp annotation.cpp quote.cpp
  typed_expr.cpp protected.cpp reducible.cpp init_module.cpp
  generic_exception.cpp fingerprint.cpp flycheck.cpp hott_kernel.cpp pp_options.cpp
  unfold_macros.cpp app_builder.cpp projection.cpp abbreviation.cpp
  relation_manager.cpp export.cpp user_recursors.cpp idx_metavar.cpp
  composition_manager.cpp noncomputable.cpp
  aux_recursors.cpp norm_num.cpp trace.cpp
  attribute_manager.cpp error_handling.cpp unification_hint.cpp
  local_context.cpp metavar_context.cpp type_context.cpp export_decl.cpp delayed_abstraction.cpp
  fun_info.cpp congr_lemma.cpp defeq_canonizer.cpp scope_pos_info_provider.cpp
  inductive.cpp mpq_macro.cpp arith_instance_manager.cpp

  # Legacy -- The following files will be eventually deleted
  normalize.cpp justification.cpp constraint.cpp metavar.cpp choice.cpp locals.cpp
  unifier.cpp match.cpp class_instance_resolution.cpp old_type_context.cpp
  legacy_type_context.cpp old_type_checker.cpp old_converter.cpp old_default_converter.cpp
  old_util.cpp let.cpp old_local_context.cpp choice_iterator.cpp
  old_tmp_type_context.cpp

  # light_lt_manager.cpp
  # proof_irrel_expr_manager.cpp
  )

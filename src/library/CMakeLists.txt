add_library(library OBJECT deep_copy.cpp expr_lt.cpp io_state.cpp
  io_state_stream.cpp bin_app.cpp constants.cpp kernel_serializer.cpp
  max_sharing.cpp shared_environment.cpp module.cpp
  private.cpp placeholder.cpp aliases.cpp
  update_declaration.cpp scoped_ext.cpp sorry.cpp replace_visitor.cpp
  explicit.cpp num.cpp string.cpp head_map.cpp
  class.cpp util.cpp print.cpp annotation.cpp quote.cpp
  typed_expr.cpp protected.cpp reducible.cpp init_module.cpp
  exception.cpp fingerprint.cpp pp_options.cpp
  unfold_macros.cpp app_builder.cpp projection.cpp relation_manager.cpp
  export.cpp user_recursors.cpp idx_metavar.cpp noncomputable.cpp
  aux_recursors.cpp norm_num.cpp trace.cpp
  attribute_manager.cpp unification_hint.cpp
  local_context.cpp metavar_context.cpp type_context.cpp export_decl.cpp delayed_abstraction.cpp
  fun_info.cpp congr_lemma.cpp defeq_canonizer.cpp
  replace_visitor_with_tc.cpp aux_definition.cpp inverse.cpp pattern_attribute.cpp choice.cpp
  locals.cpp normalize.cpp discr_tree.cpp
  mt_task_queue.cpp st_task_queue.cpp
  library_task_builder.cpp
  eval_helper.cpp
  messages.cpp message_builder.cpp module_mgr.cpp comp_val.cpp
  documentation.cpp check.cpp arith_instance.cpp parray.cpp process.cpp
  pipe.cpp handle.cpp profiling.cpp time_task.cpp abstract_context_cache.cpp
  context_cache.cpp unique_id.cpp persistent_context_cache.cpp elab_context.cpp)

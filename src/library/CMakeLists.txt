add_library(library OBJECT expr_lt.cpp io_state.cpp
  io_state_stream.cpp bin_app.cpp constants.cpp max_sharing.cpp
  module.cpp placeholder.cpp sorry.cpp replace_visitor.cpp num.cpp
  class.cpp util.cpp print.cpp annotation.cpp
  protected.cpp reducible.cpp init_module.cpp exception.cpp
  pp_options.cpp projection.cpp
  idx_metavar.cpp aux_recursors.cpp trace.cpp
  local_context.cpp metavar_context.cpp
  type_context.cpp
  locals.cpp messages.cpp message_builder.cpp check.cpp
  profiling.cpp time_task.cpp
  scope_pos_info_provider.cpp formatter.cpp json.cpp
  pos_info_provider.cpp abstract_type_context.cpp aux_match.cpp)

add_library(lean_frontend tokens.cpp register_module.cpp
token_table.cpp scanner.cpp parse_table.cpp parser_config.cpp
parser.cpp parser_pos_provider.cpp builtin_cmds.cpp builtin_exprs.cpp
server.cpp notation_cmd.cpp calc.cpp decl_cmds.cpp util.cpp
inductive_cmd.cpp elaborator.cpp dependencies.cpp parser_bindings.cpp
begin_end_ext.cpp tactic_hint.cpp pp.cpp theorem_queue.cpp
structure_cmd.cpp info_manager.cpp info_annotation.cpp find_cmd.cpp
coercion_elaborator.cpp info_tactic.cpp
init_module.cpp elaborator_context.cpp calc_proof_elaborator.cpp
parse_tactic_location.cpp parse_rewrite_tactic.cpp
type_util.cpp elaborator_exception.cpp migrate_cmd.cpp)

target_link_libraries(lean_frontend ${LEAN_LIBS})

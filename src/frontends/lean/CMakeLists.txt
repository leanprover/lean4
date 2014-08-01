add_library(lean_frontend register_module.cpp token_table.cpp
scanner.cpp parse_table.cpp parser_config.cpp parser.cpp
parser_pos_provider.cpp builtin_cmds.cpp builtin_exprs.cpp
interactive.cpp notation_cmd.cpp calc.cpp
decl_cmds.cpp util.cpp inductive_cmd.cpp elaborator.cpp
dependencies.cpp parser_bindings.cpp proof_qed_ext.cpp
class.cpp pp_options.cpp tactic_hint.cpp pp.cpp theorem_queue.cpp
structure_cmd.cpp sorry.cpp)

target_link_libraries(lean_frontend ${LEAN_LIBS})

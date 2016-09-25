add_library(lean_frontend OBJECT tokens.cpp
token_table.cpp scanner.cpp parse_table.cpp parser_config.cpp
parser.cpp parser_pos_provider.cpp builtin_cmds.cpp builtin_exprs.cpp
notation_cmd.cpp calc.cpp decl_cmds.cpp util.cpp
inductive_cmds.cpp dependencies.cpp
pp.cpp structure_cmd.cpp structure_instance.cpp
init_module.cpp type_util.cpp local_ref_info.cpp decl_attributes.cpp nested_declaration.cpp
opt_cmd.cpp prenum.cpp print_cmd.cpp elaborator.cpp
match_expr.cpp local_context_adapter.cpp decl_util.cpp definition_cmds.cpp
brackets.cpp begin_end_block.cpp)

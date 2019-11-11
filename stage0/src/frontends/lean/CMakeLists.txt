add_library(lean_frontend OBJECT tokens.cpp
token_table.cpp scanner.cpp parse_table.cpp parser_config.cpp
parser.cpp builtin_cmds.cpp builtin_exprs.cpp
notation_cmd.cpp decl_cmds.cpp util.cpp
inductive_cmds.cpp pp.cpp structure_cmd.cpp structure_instance.cpp
init_module.cpp type_util.cpp decl_attributes.cpp
prenum.cpp print_cmd.cpp elaborator.cpp
match_expr.cpp local_context_adapter.cpp decl_util.cpp definition_cmds.cpp
brackets.cpp json.cpp typed_expr.cpp choice.cpp lean_elaborator.cpp)

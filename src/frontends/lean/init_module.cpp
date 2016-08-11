/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/tokens.h"
#include "frontends/lean/pattern_attribute.h"
#include "frontends/lean/elaborator_context.h"
#include "frontends/lean/old_elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_annotation.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/builtin_cmds.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/inductive_cmd.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/server.h"
#include "frontends/lean/local_ref_info.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/nested_declaration.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/old_attributes.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/match_expr.h"

namespace lean {
void initialize_frontend_lean_module() {
    initialize_pattern_attribute();
    initialize_old_attributes();
    initialize_prenum();
    initialize_info_annotation();
    initialize_tokens();
    initialize_token_table();
    initialize_parse_table();
    initialize_builtin_cmds();
    initialize_builtin_exprs();
    initialize_elaborator_context();
    initialize_old_elaborator();
    initialize_scanner();
    initialize_parser();
    initialize_parser_config();
    initialize_calc();
    initialize_inductive_cmd();
    initialize_inductive_cmds();
    initialize_structure_cmd();
    initialize_info_manager();
    initialize_pp();
    initialize_server();
    initialize_local_ref_info();
    initialize_decl_cmds();
    initialize_nested_declaration();
    initialize_match_expr();
    initialize_elaborator();
}
void finalize_frontend_lean_module() {
    finalize_elaborator();
    finalize_match_expr();
    finalize_old_attributes();
    finalize_nested_declaration();
    finalize_decl_cmds();
    finalize_local_ref_info();
    finalize_server();
    finalize_pp();
    finalize_info_manager();
    finalize_structure_cmd();
    finalize_inductive_cmds();
    finalize_inductive_cmd();
    finalize_calc();
    finalize_parser_config();
    finalize_parser();
    finalize_scanner();
    finalize_old_elaborator();
    finalize_elaborator_context();
    finalize_builtin_exprs();
    finalize_builtin_cmds();
    finalize_parse_table();
    finalize_token_table();
    finalize_tokens();
    finalize_info_annotation();
    finalize_prenum();
    finalize_pattern_attribute();
}
}

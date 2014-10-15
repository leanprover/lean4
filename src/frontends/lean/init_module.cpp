/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/tokens.h"
#include "frontends/lean/elaborator_context.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/pp_options.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/no_info.h"
#include "frontends/lean/extra_info.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/class.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/builtin_cmds.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/builtin_tactics.h"
#include "frontends/lean/inductive_cmd.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/server.h"

namespace lean {
void initialize_frontend_lean_module() {
    initialize_tokens();
    initialize_token_table();
    initialize_parse_table();
    initialize_builtin_cmds();
    initialize_builtin_tactics();
    initialize_builtin_exprs();
    initialize_elaborator_context();
    initialize_elaborator();
    initialize_pp_options();
    initialize_scanner();
    initialize_parser();
    initialize_no_info();
    initialize_extra_info();
    initialize_tactic_hint();
    initialize_class();
    initialize_parser_config();
    initialize_calc();
    initialize_begin_end_ext();
    initialize_inductive_cmd();
    initialize_structure_cmd();
    initialize_info_manager();
    initialize_pp();
    initialize_server();
}
void finalize_frontend_lean_module() {
    finalize_server();
    finalize_pp();
    finalize_info_manager();
    finalize_structure_cmd();
    finalize_inductive_cmd();
    finalize_begin_end_ext();
    finalize_calc();
    finalize_parser_config();
    finalize_class();
    finalize_tactic_hint();
    finalize_extra_info();
    finalize_no_info();
    finalize_parser();
    finalize_scanner();
    finalize_pp_options();
    finalize_elaborator();
    finalize_elaborator_context();
    finalize_builtin_exprs();
    finalize_builtin_tactics();
    finalize_builtin_cmds();
    finalize_parse_table();
    finalize_token_table();
    finalize_tokens();
}
}

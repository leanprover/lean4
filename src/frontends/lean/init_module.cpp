/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/tokens.h"
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

namespace lean {
void initialize_frontend_lean_module() {
    initialize_tokens();
    initialize_elaborator();
    initialize_pp_options();
    initialize_parser();
    initialize_no_info();
    initialize_extra_info();
    initialize_tactic_hint();
    initialize_class();
    initialize_parser_config();
    initialize_calc();
    initialize_begin_end_ext();
}
void finalize_frontend_lean_module() {
    finalize_begin_end_ext();
    finalize_calc();
    finalize_parser_config();
    finalize_class();
    finalize_tactic_hint();
    finalize_tokens();
    finalize_extra_info();
    finalize_no_info();
    finalize_parser();
    finalize_pp_options();
    finalize_elaborator();
}
}

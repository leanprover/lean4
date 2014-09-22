/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/elaborator.h"
#include "frontends/lean/pp_options.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/no_info.h"
#include "frontends/lean/extra_info.h"

namespace lean {
void initialize_frontend_lean_module() {
    initialize_elaborator();
    initialize_pp_options();
    initialize_parser();
    initialize_no_info();
    initialize_extra_info();
}
void finalize_frontend_lean_module() {
    finalize_extra_info();
    finalize_no_info();
    finalize_parser();
    finalize_pp_options();
    finalize_elaborator();
}
}

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/init_module.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/expr.h"
#include "kernel/level.h"
#include "kernel/declaration.h"
#include "kernel/local_ctx.h"
#include "kernel/inductive.h"
#include "kernel/quot.h"
#include "kernel/trace.h"

namespace lean {
void initialize_kernel_module() {
    initialize_level();
    initialize_expr();
    initialize_declaration();
    initialize_type_checker();
    initialize_environment();
    initialize_local_ctx();
    initialize_inductive();
    initialize_quot();
    initialize_trace();
}

void finalize_kernel_module() {
    finalize_trace();
    finalize_quot();
    finalize_inductive();
    finalize_local_ctx();
    finalize_environment();
    finalize_type_checker();
    finalize_declaration();
    finalize_expr();
    finalize_level();
}
}

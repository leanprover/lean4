/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/old_type_checker.h"
#include "kernel/expr.h"
#include "kernel/formatter.h"
#include "kernel/level.h"
#include "kernel/declaration.h"
#include "kernel/error_msgs.h"
#include "kernel/local_ctx.h"
#include "kernel/quot.h"

namespace lean {
void initialize_kernel_module() {
    initialize_error_msgs();
    initialize_level();
    initialize_expr();
    initialize_declaration();
    initialize_old_type_checker();
    initialize_environment();
    initialize_formatter();
    initialize_quot();
    initialize_local_ctx();
}

void finalize_kernel_module() {
    finalize_local_ctx();
    finalize_quot();
    finalize_formatter();
    finalize_environment();
    finalize_old_type_checker();
    finalize_declaration();
    finalize_expr();
    finalize_level();
    finalize_error_msgs();
}
}

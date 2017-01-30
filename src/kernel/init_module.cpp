/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/expr.h"
#include "kernel/formatter.h"
#include "kernel/level.h"
#include "kernel/declaration.h"
#include "kernel/error_msgs.h"

namespace lean {
void initialize_kernel_module() {
    initialize_error_msgs();
    initialize_level();
    initialize_expr();
    initialize_declaration();
    initialize_type_checker();
    initialize_environment();
    initialize_formatter();
}
void finalize_kernel_module() {
    finalize_formatter();
    finalize_environment();
    finalize_type_checker();
    finalize_declaration();
    finalize_expr();
    finalize_level();
    finalize_error_msgs();
}
}

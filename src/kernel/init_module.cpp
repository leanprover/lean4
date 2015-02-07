/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/environment.h"
#include "kernel/converter.h"
#include "kernel/type_checker.h"
#include "kernel/expr.h"
#include "kernel/formatter.h"
#include "kernel/level.h"
#include "kernel/declaration.h"
#include "kernel/default_converter.h"

namespace lean {
void initialize_kernel_module() {
    initialize_level();
    initialize_expr();
    initialize_declaration();
    initialize_default_converter();
    initialize_converter();
    initialize_type_checker();
    initialize_environment();
    initialize_formatter();
}
void finalize_kernel_module() {
    finalize_formatter();
    finalize_environment();
    finalize_type_checker();
    finalize_converter();
    finalize_default_converter();
    finalize_declaration();
    finalize_expr();
    finalize_level();
}
}

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/stackinfo.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "kernel/inductive/inductive.h"
#include "library/init_module.h"
#include "library/tactic/init_module.h"
#include "library/print.h"
#include "frontends/lean/init_module.h"
#include "frontends/lua/register_modules.h"
#include "init/init.h"

namespace lean {
void initialize() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_inductive_module();
    initialize_library_module();
    initialize_tactic_module();
    initialize_frontend_lean_module();
    init_default_print_fn();
    register_modules();
}
void finalize() {
    finalize_frontend_lean_module();
    finalize_tactic_module();
    finalize_library_module();
    finalize_inductive_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
}

initializer::initializer() {
    initialize();
}

initializer::~initializer() {
    finalize();
}
}

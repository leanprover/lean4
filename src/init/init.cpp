/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/tactic/init_module.h"
#include "frontends/lean/init_module.h"
#include "init/init.h"

namespace lean {
void initialize() {
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_module();
    initialize_tactic_module();
    initialize_frontend_lean_module();
}
void finalize() {
    finalize_frontend_lean_module();
    finalize_tactic_module();
    finalize_library_module();
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

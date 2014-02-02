/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/io_state.h"
#include "kernel/decl_macros.h"
#include "kernel/kernel_decls.cpp"

namespace lean {
// =======================================
// Bultin universe variables m and u
static level u_lvl(name("U"));
expr const TypeU = Type(u_lvl);
expr const TypeU1 = Type(u_lvl+1);
// =======================================

// =======================================
// Boolean Type
expr const Bool  = mk_Bool();
expr const True  = mk_true();
expr const False = mk_false();
expr mk_bool_type() { return mk_Bool(); }
bool is_bool(expr const & t) { return is_Bool(t); }
// =======================================

expr mk_bool_value(bool v) {
    return v ? True : False;
}
bool is_bool_value(expr const & e) {
    return is_true(e) || is_false(e);
}
bool to_bool(expr const & e) {
    lean_assert(is_bool_value(e));
    return e == True;
}
// =======================================

void import_kernel(environment const & env, io_state const & ios) {
    env->import("kernel", ios);
}
}

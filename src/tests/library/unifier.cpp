/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/unifier.h"
using namespace lean;

static void tst1() {
    environment env;
    expr Type = mk_Type();
    expr A  = Local("A", Type);
    expr f  = Local("f", A >> (A >> A));
    expr a  = Local("a", A);
    expr b  = Local("b", A);
    expr m  = mk_metavar("m", A);
    expr t1 = mk_app(f, m, m);
    expr t2 = mk_app(f, a, b);
    auto r = unify(env, t1, t2, name_generator("foo"));
    lean_assert(!r.pull());
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_module();
    tst1();
    finalize_library_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}

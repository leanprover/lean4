/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/deep_copy.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr a = Const("a");
    expr x = Var(0);
    expr Type = mk_Type();
    expr t = Type;
    expr z = Const("z");
    expr m = mk_metavar("a", Type);
    expr F = mk_pi("y", t, mk_lambda("x", t, mk_app(f, mk_app(f, mk_app(f, x, a), Const("10")), mk_app(f, x, m))));
    expr G = deep_copy(F);
    lean_assert(F == G);
    lean_assert(!is_eqp(F, G));
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

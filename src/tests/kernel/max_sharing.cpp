/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/abstract.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
#include "library/max_sharing.h"
#include "library/print.h"
using namespace lean;

static void tst1() {
    max_sharing_fn max_fn;
    expr a1 = mk_const("a");
    expr a2 = mk_const("a");
    expr N = mk_const("N");
    expr x = mk_local("x", N);
    expr y = mk_local("y", N);
    expr f = mk_const("f");
    expr F1, F2;
    F1 = mk_app(f, Fun(x, mk_app(f, x, x)), Fun(y, mk_app(f, y, y)));
    lean_assert(!is_eqp(app_arg(app_fn(F1)), app_arg(F1)));
    F2 = max_fn(F1);
    std::cout << F2 << "\n";
    lean_assert(!is_eqp(app_arg(app_fn(F2)), app_arg(F2))); // name matter
    max_fn.clear();
}

static void tst2() {
    max_sharing_fn max_fn1;
    max_sharing_fn max_fn2;
    expr x   = mk_const("x");
    expr f   = mk_const("f");
    expr g   = mk_const("g");
    expr t1  = max_fn2(max_fn1(mk_app(f, mk_app(g, x))));
    expr t2  = max_fn2(mk_app(f, t1, mk_app(g, x)));
    expr arg1 = app_arg(app_arg(app_fn(t2)));
    expr arg2 = app_arg(t2);
    lean_assert(is_eqp(arg1, arg2));
}

static void tst3() {
    max_sharing_fn max_fn;
    expr a1 = mk_const("a");
    expr a2 = mk_const("a");
    expr a3 = mk_const("a");
    expr g  = mk_const("g");
    expr f  = mk_const("f");
    expr new_a1 = max_fn(a1);
    lean_assert(is_eqp(new_a1, a1));
    expr t1 = max_fn(mk_app(f, a2));
    lean_assert(is_eqp(app_arg(t1), a1));
    expr t2 = max_fn(mk_app(f, a2));
    lean_assert(is_eqp(t1, t2));
    expr t3 = max_fn(mk_app(f, a3));
    lean_assert(is_eqp(t1, t3));
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    initialize_library_core_module();
    initialize_library_module();
    init_default_print_fn();
    tst1();
    tst2();
    tst3();
    finalize_library_module();
    finalize_library_core_module();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}

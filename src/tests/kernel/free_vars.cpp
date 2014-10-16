/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/init_module.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr x = Var(0);
    expr y = Var(1);
    expr t = Const("t");
    expr F = mk_lambda("_", t, mk_app(f, x));
    lean_assert(has_free_var(mk_lambda("_", t, mk_app(f, Var(1))), 0));
    lean_assert(!has_free_var(mk_lambda("_", t, mk_app(f, Var(0))), 1));
    lean_assert(!has_free_var(mk_pi("_", t, mk_lambda("_", t, mk_app(f, Var(1)))), 0));
    lean_assert(has_free_var(mk_app(f, Var(0)), 0));
    lean_assert(has_free_var(mk_app(f, Var(1)), 1));
    lean_assert(!has_free_var(mk_app(f, Var(1)), 0));
    lean_assert_eq(lower_free_vars(mk_app(f, Var(1)), 1), mk_app(f, Var(0)));
    lean_assert_eq(lower_free_vars(mk_lambda("_", t, mk_app(f, Var(2))), 1), mk_lambda("_", t, mk_app(f, Var(1))));
    lean_assert_eq(lower_free_vars(mk_lambda("_", t, mk_app(f, Var(0))), 1), mk_lambda("_", t, mk_app(f, Var(0))));
}

static void tst2() {
    expr f = Const("f");
    expr B = Const("Prop");
    expr x = Local("x", B);
    expr y = Local("y", B);
    expr t = Fun({x, y}, x);
    lean_assert(closed(t));
    lean_assert(!closed(binding_body(t)));
}

static void tst3() {
    unsigned n = 20000;
    unsigned m = 10;
    expr f = Const("f");
    expr a = Const("a");
    expr r = mk_app(f, a, Var(m));
    expr b = Const("Prop");
    for (unsigned i = 0; i < n; i++)
        r = mk_lambda(name(), b, r);
    lean_assert(closed(r));
    bool flag = true;
    while (is_lambda(r)) {
        flag = flag && closed(r);
        r = binding_body(r);
    }
}

static void tst4() {
    expr f = Const("f");
    expr B = mk_Prop();
    expr x = Local("x", B);
    expr y = Local("y", B);
    expr t = mk_app(f, mk_app(Fun({x, y}, mk_app(f, x, y)), mk_app(f, Var(1), Var(2))), x);
    lean_assert_eq(lift_free_vars(t, 1, 2),
                   mk_app(f, mk_app(Fun(x, Fun(y, mk_app(f, x, y))), mk_app(f, Var(3), Var(4))), x));
    lean_assert_eq(lift_free_vars(t, 0, 3),
                   mk_app(f, mk_app(Fun(x, Fun(y, mk_app(f, x, y))), mk_app(f, Var(4), Var(5))), x));
    lean_assert_eq(lift_free_vars(t, 3, 2), t);
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    tst1();
    tst2();
    tst3();
    tst4();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}

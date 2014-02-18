/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr x = Var(0);
    expr y = Var(1);
    expr t = Const("t");
    expr F = mk_lambda("_", t, f(x));
    lean_assert(has_free_var(mk_lambda("_", t, f(Var(1))), 0));
    lean_assert(!has_free_var(mk_lambda("_", t, f(Var(0))), 1));
    lean_assert(!has_free_var(mk_pi("_", t, mk_lambda("_", t, f(Var(1)))), 0));
    lean_assert(has_free_var(f(Var(0)), 0));
    lean_assert(has_free_var(f(Var(1)), 1));
    lean_assert(!has_free_var(f(Var(1)), 0));
    lean_assert(has_free_var(f(Var(1)), 0, 2));
    lean_assert(!has_free_var(f(Var(1)), 0, 1));
    lean_assert_eq(lower_free_vars(f(Var(1)), 1), f(Var(0)));
    lean_assert_eq(lower_free_vars(mk_lambda("_", t, f(Var(2))), 1), mk_lambda("_", t, f(Var(1))));
    lean_assert_eq(lower_free_vars(mk_lambda("_", t, f(Var(0))), 1), mk_lambda("_", t, f(Var(0))));
}

static void tst2() {
    expr f = Const("f");
    expr x = Const("x");
    expr y = Const("y");
    expr B = Const("Bool");
    expr t = Fun({x, B}, Fun({y, B}, x));
    lean_assert(closed(t));
    lean_assert(!closed(binder_body(t)));
}

static void tst3() {
    unsigned n = 20000;
    unsigned m = 10;
    expr f = Const("f");
    expr a = Const("a");
    expr r = f(a, Var(m));
    expr b = Const("Bool");
    for (unsigned i = 0; i < n; i++)
        r = mk_lambda(name(), b, r);
    lean_assert(closed(r));
    bool flag = true;
    while (is_lambda(r)) {
        flag = flag && closed(r);
        r = binder_body(r);
    }
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}

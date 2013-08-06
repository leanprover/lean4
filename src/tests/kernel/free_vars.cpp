/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "free_vars.h"
#include "test.h"
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
    lean_assert(lower_free_vars(f(Var(1)), 1) == f(Var(0)));
    lean_assert(lower_free_vars(mk_lambda("_", t, f(Var(2))), 1) == mk_lambda("_", t, f(Var(1))));
    lean_assert(lower_free_vars(mk_lambda("_", t, f(Var(0))), 1) == mk_lambda("_", t, f(Var(0))));
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

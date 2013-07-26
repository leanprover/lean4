/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "free_vars.h"
#include "test.h"
using namespace lean;

static void tst1() {
    expr f = constant("f");
    expr a = constant("a");
    expr b = constant("b");
    expr x = var(0);
    expr y = var(1);
    expr t = constant("t");
    expr F = lambda("_", t, f(x));
    lean_assert(has_free_var(lambda("_", t, f(var(1))), 0));
    lean_assert(!has_free_var(lambda("_", t, f(var(0))), 1));
    lean_assert(!has_free_var(pi("_", t, lambda("_", t, f(var(1)))), 0));
    lean_assert(has_free_var(f(var(0)), 0));
    lean_assert(has_free_var(f(var(1)), 1));
    lean_assert(!has_free_var(f(var(1)), 0));
    lean_assert(has_free_var(f(var(1)), 0, 2));
    lean_assert(!has_free_var(f(var(1)), 0, 1));
    lean_assert(lower_free_vars(f(var(1)), 1) == f(var(0)));
    lean_assert(lower_free_vars(lambda("_", t, f(var(2))), 1) == lambda("_", t, f(var(1))));
    lean_assert(lower_free_vars(lambda("_", t, f(var(0))), 1) == lambda("_", t, f(var(0))));
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

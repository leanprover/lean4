/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "kernel/abstract.h"
#include "kernel/max_sharing.h"
using namespace lean;

static void tst1() {
    max_sharing_fn max_fn;
    expr a1 = Const("a");
    expr a2 = Const("a");
    expr x = Const("x");
    expr y = Const("y");
    expr f = Const("f");
    expr N = Const("N");
    expr F1, F2;
    F1 = f(Fun({x, N}, f(x, x)), Fun({y, N}, f(y, y)));
    lean_assert(!is_eqp(app_arg(app_fn(F1)), app_arg(F1)));
    F2 = max_fn(F1);
    std::cout << F2 << "\n";
    lean_assert(is_eqp(app_arg(app_fn(F2)), app_arg(F2)));
    max_fn.clear();
    F1 = f(Let(x, Type, f(a1), f(x, x)), Let(y, Type, f(a1), f(y, y)));
    lean_assert(!is_eqp(app_arg(app_fn(F1)), app_arg(F1)));
    F2 = max_fn(F1);
    std::cout << F2 << "\n";
    lean_assert(is_eqp(app_arg(app_fn(F2)), app_arg(F2)));
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}

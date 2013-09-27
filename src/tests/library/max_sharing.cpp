/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "kernel/abstract.h"
#include "library/max_sharing.h"
#include "library/printer.h"
using namespace lean;

static void tst1() {
    max_sharing_fn max_fn;
    expr a1 = Const("a");
    expr a2 = Const("a");
    expr F1 = Eq(a1, a2);
    lean_assert(!is_eqp(eq_lhs(F1), eq_rhs(F1)));
    expr F2 = max_fn(F1);
    lean_assert(is_eqp(eq_lhs(F2), eq_rhs(F2)));
    expr x = Const("x");
    expr y = Const("y");
    expr f = Const("f");
    expr N = Const("N");
    F1 = f(Fun({x, N}, f(x, x)), Fun({y, N}, f(y, y)));
    lean_assert(!is_eqp(arg(F1, 1), arg(F1, 2)));
    F2 = max_fn(F1);
    std::cout << F2 << "\n";
    lean_assert(is_eqp(arg(F2, 1), arg(F2, 2)));
    max_fn.clear();
    local_context lctx{mk_lift(1, 1), mk_inst(0, a1)};
    expr m1 = mk_metavar("m1", expr(), lctx);
    expr m2 = mk_metavar("m1", expr(), lctx);
    F1 = f(m1, m2);
    lean_assert(!is_eqp(arg(F1, 1), arg(F1, 2)));
    F2 = max_fn(F1);
    std::cout << F2 << "\n";
    lean_assert(is_eqp(arg(F2, 1), arg(F2, 2)));
    F1 = f(Let({x, f(a1)}, f(x, x)), Let({y, f(a1)}, f(y, y)));
    lean_assert(!is_eqp(arg(F1, 1), arg(F1, 2)));
    F2 = max_fn(F1);
    std::cout << F2 << "\n";
    lean_assert(is_eqp(arg(F2, 1), arg(F2, 2)));
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

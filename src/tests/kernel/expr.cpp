/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "expr.h"
#include "test.h"
using namespace lean;

static void tst1() {
    expr a;
    a = numeral(mpz(10));
    expr f;
    f = var(0);
    expr fa = app({f, a});
    std::cout << fa << "\n";
    std::cout << app({fa, a}) << "\n";
    lean_assert(eqp(get_arg(fa, 0), f));
    lean_assert(eqp(get_arg(fa, 1), a));
    lean_assert(!eqp(fa, app({f, a})));
    lean_assert(app({fa, a}) == app({f, a, a}));
    std::cout << app({fa, fa, fa}) << "\n";
    std::cout << lambda(name("x"), prop(), var(0)) << "\n";
}

expr mk_dag(unsigned depth) {
    expr f = constant(name("f"));
    expr a = var(0);
    while (depth > 0) {
        depth--;
        a = app({f, a, a});
    }
    return a;
}

static void tst2() {
    expr r1 = mk_dag(24);
    expr r2 = mk_dag(24);
    lean_verify(r1 == r2);
}

int main() {
    // continue_on_violation(true);
    std::cout << "sizeof(expr):     " << sizeof(expr) << "\n";
    std::cout << "sizeof(expr_app): " << sizeof(expr_app) << "\n";
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

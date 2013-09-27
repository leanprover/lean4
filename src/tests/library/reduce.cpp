/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "library/reduce.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr h = Const("h");
    expr x = Const("x");
    expr y = Const("y");
    expr a = Const("a");
    expr b = Const("b");
    expr c = Const("c");
    expr d = Const("d");
    expr N = Const("N");
    expr F1 = Fun({x, N}, x)(f, a);
    lean_assert(is_head_beta(F1));
    std::cout << F1 << " --> " << head_beta_reduce(F1) << "\n";
    lean_assert_eq(head_beta_reduce(F1), f(a));
    expr F2 = Fun({{h, N >> (N >> (N >> N))}, {y, N}}, h(y))(f, a, b, c);
    lean_assert(is_head_beta(F2));
    std::cout << F2 << " --> " << head_beta_reduce(F2) << "\n";
    lean_assert_eq(head_beta_reduce(F2), f(a, b, c));
    expr F3 = Fun({x, N}, f(Fun({y, N}, y)(x), x))(a);
    lean_assert(is_head_beta(F3));
    std::cout << F3 << " --> " << head_beta_reduce(F3) << "\n";
    lean_assert_eq(head_beta_reduce(F3), f(Fun({y, N}, y)(a), a));
    std::cout << F3 << " --> " << beta_reduce(F3) << "\n";
    lean_assert_eq(beta_reduce(F3), f(a, a));
}

static void tst2() {
    environment env;
    expr x = Const("x");
    expr a = Const("a");
    expr f = Const("f");
    expr N = Const("N");
    expr F1 = Let({x, a}, f(x));
    lean_assert_eq(head_beta_reduce(F1), F1);
    lean_assert_eq(head_reduce(F1, env), f(a));
    context ctx;
    ctx = extend(ctx, "x", N, f(a));
    ctx = extend(ctx, "y", N, f(Var(0)));
    std::cout << head_reduce(Var(0), env, ctx) << "\n";
    lean_assert_eq(head_reduce(Var(0), env, ctx), f(Var(1)));
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}



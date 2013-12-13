/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/metavar.h"
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
    expr x = Const("x");
    expr a = Const("a");
    expr f = Const("f");
    expr N = Const("N");
    expr F1 = Let({x, a}, f(x));
    lean_assert_eq(head_beta_reduce(F1), F1);
}

static void tst3() {
    metavar_env menv;
    expr f  = Const("f");
    expr a  = Const("a");
    expr T  = Const("T");
    expr m1 = menv->mk_metavar();
    expr m2 = menv->mk_metavar(context({{"x", T}, {"y", T}}));
    lean_assert_eq(instantiate(f(m1, Var(0)), 0, a, menv), f(m1, a));
    lean_assert_ne(instantiate(f(m1, Var(0)), 0, a, menv), instantiate(f(m1, Var(0)), 0, a));
    lean_assert_ne(instantiate(f(m2, Var(0)), 0, a, menv), f(m2, a));
    lean_assert_eq(instantiate(f(m2, Var(0)), 0, a, menv), f(add_inst(m2, 0, a), a));
    expr x = Const("x");
    lean_assert_eq(instantiate(Fun({x, T}, f(m1, Var(1), Var(0))), 0, f(Var(0)), menv),
                   Fun({x, T}, f(m1, f(Var(1)), Var(0))));
    lean_assert_eq(instantiate(Fun({x, T}, f(m2, Var(1), Var(0))), 0, f(Var(0)), menv),
                   Fun({x, T}, f(add_inst(m2, 1, f(Var(1))), f(Var(1)), Var(0))));
    lean_assert_eq(instantiate(Fun({x, T}, f(m2, Var(3), Var(0))), 2, f(Var(0)), menv),
                   Fun({x, T}, f(m2, f(Var(1)), Var(0))));
    lean_assert_eq(instantiate(Fun({x, T}, f(m1, Var(3), Var(0))), 2, f(Var(0)), menv),
                   Fun({x, T}, f(m1, f(Var(1)), Var(0))));
    lean_assert_eq(instantiate(Fun({x, T}, f(m2, Var(3), Var(0))), 1, f(Var(0)), menv),
                   Fun({x, T}, f(m2, Var(2), Var(0))));
    expr m3 = menv->mk_metavar(context({{"x", T}, {"y", T}, {"z", T}}));
    lean_assert_eq(instantiate(Fun({x, T}, f(m3, Var(3), Var(0))), 1, f(Var(0)), menv),
                   Fun({x, T}, f(add_inst(m3, 2, f(Var(1))), Var(2), Var(0))));
}

static void tst4() {
    metavar_env menv;
    expr T  = Const("T");
    expr m1 = menv->mk_metavar();
    expr m2 = menv->mk_metavar(context({{"x", T}, {"y", T}}));
    expr f = Const("f");
    expr g = Const("f");
    expr x = Const("x");
    expr a = Const("a");
    expr F1 = Fun({x, T}, g(x, m1))(a);
    expr F2 = Fun({x, T}, g(x, m2))(a);
    lean_assert_eq(head_beta_reduce(F1, menv), g(a, m1));
    lean_assert_eq(head_beta_reduce(F1), g(a, add_inst(m1, 0, a)));
    lean_assert_eq(head_beta_reduce(F2, menv), g(a, add_inst(m2, 0, a)));
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}

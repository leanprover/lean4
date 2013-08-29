/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "test.h"
#include "metavar.h"
#include "abstract.h"
#include "printer.h"
using namespace lean;

static void tst1() {
    expr N  = Const("N");
    expr f  = Const("f");
    expr x  = Const("x");
    expr y  = Const("y");
    expr a  = Const("a");
    expr g  = Const("g");
    expr h  = Const("h");
    expr m1 = mk_metavar(1);
    expr m2 = mk_metavar(2);
    expr t = f(Var(0), Fun({x, N}, f(Var(1), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate_free_var_mmv(t, 0, g(m1, m2));
    std::cout << r << std::endl;
    r = instantiate_metavar(r, 2, Var(2));
    std::cout << r << std::endl;
    r = instantiate_metavar(r, 1, h(Var(3)));
    std::cout << r << std::endl;
    lean_assert(r == f(g(h(Var(3)), Var(2)), Fun({x, N}, f(g(h(Var(4)), Var(3)), x, Fun({y, N}, f(g(h(Var(5)), Var(4)), x, y))))));
}

static void tst2() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr m1 = mk_metavar(1);
    expr t  = f(m1, Var(0));
    expr r = instantiate_free_var_mmv(t, 0, a);
    r = instantiate_metavar(r, 1, g(Var(0)));
    std::cout << r << std::endl;
    lean_assert(r == f(g(a), a));
}

static void tst3() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr m1 = mk_metavar(1);
    expr t  = f(m1, Var(0), Var(2));
    expr r = instantiate_free_var_mmv(t, 0, a);
    r = instantiate_metavar(r, 1, g(Var(0), Var(1)));
    std::cout << r << std::endl;
    lean_assert(r == f(g(a,Var(0)), a, Var(1)));
}

static void tst4() {
    expr f  = Const("f");
    expr g  = Const("g");
    expr a  = Const("a");
    expr m1 = mk_metavar(1);
    expr t  = f(m1, Var(1), Var(2));
    expr r  = lift_free_vars_mmv(t, 1, 2);
    std::cout << r << std::endl;
    r = instantiate_free_var_mmv(r, 0, a);
    std::cout << r << std::endl;
    r = instantiate_metavar(r, 1, g(Var(0), Var(1)));
    std::cout << r << std::endl;
    lean_assert(r == f(g(a,Var(2)), Var(2), Var(3)));
}

static void tst5() {
    expr N  = Const("N");
    expr f  = Const("f");
    expr x  = Const("x");
    expr y  = Const("y");
    expr a  = Const("a");
    expr g  = Const("g");
    expr h  = Const("h");
    expr m1 = mk_metavar(1);
    expr m2 = mk_metavar(2);
    expr t = f(Var(0), Fun({x, N}, f(Var(1), Var(2), x, Fun({y, N}, f(Var(2), x, y)))));
    expr r = instantiate_free_var_mmv(t, 0, g(m1));
    std::cout << r << std::endl;
    r = instantiate_free_var_mmv(r, 0, h(m2));
    std::cout << r << std::endl;
    r = instantiate_metavar(r, 1, f(Var(0)));
    std::cout << r << std::endl;
    r = instantiate_metavar(r, 2, Var(2));
    std::cout << r << std::endl;
    lean_assert(r == f(g(f(h(Var(2)))), Fun({x, N}, f(g(f(h(Var(3)))), h(Var(3)), x, Fun({y, N}, f(g(f(h(Var(4)))), x, y))))));
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    return has_violations() ? 1 : 0;
}



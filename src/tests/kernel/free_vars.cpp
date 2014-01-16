/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/metavar.h"
#include "kernel/kernel.h"
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
    lean_assert(!closed(abst_body(t)));
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
        r = abst_body(r);
    }
}

static void tst4() {
    metavar_env menv;
    auto fn = [&](expr const & e) { return free_var_range(e, menv); };
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr x = Const("x");
    expr m1 = menv->mk_metavar();
    lean_assert(fn(m1) == 0);
    lean_assert(fn(Var(0)) == 1);
    lean_assert(fn(Var(0)(Var(2), Var(1))) == 3);
    lean_assert(fn(Type()) == 0);
    lean_assert(fn(Bool) == 0);
    lean_assert(fn(Fun({x, Type()}, Var(0))) == 0);
    lean_assert(fn(Fun({x, Var(0)}, Var(0))) == 1);
    lean_assert(fn(Fun({x, Var(0)}, Var(2))) == 2);
    lean_assert(fn(Fun({x, Var(0)}, HEq(Var(2), Var(1)))) == 2);
    lean_assert(fn(Pi({x, Type()}, Var(0))) == 0);
    lean_assert(fn(Pi({x, Var(0)}, Var(0))) == 1);
    lean_assert(fn(Pi({x, Var(0)}, Var(2))) == 2);
    lean_assert(fn(Pi({x, Var(0)}, HEq(Var(2), Var(1)))) == 2);
    context ctx;
    ctx = extend(ctx, name("x"), Bool);
    ctx = extend(ctx, name("y"), Bool);
    expr m2 = menv->mk_metavar(ctx);
    lean_assert_eq(fn(m2), 2);
    lean_assert_eq(fn(add_lift(m2, 3, 5)), 2);
    lean_assert_eq(fn(add_lift(m2, 2, 5)), 2);
    lean_assert_eq(fn(add_lift(m2, 1, 5)), 7);
    lean_assert_eq(fn(add_inst(m2, 3, Var(10))), 2);
    lean_assert_eq(fn(add_inst(m2, 1, Var(10))), 11);
    // Here is the explanation for the following assertion.
    // If m2 is assigned to #1, that m2[1:f(#2)] becomes f(#2),
    // and then lift:2:2 transforms it to f(#4)
    lean_assert_eq(fn(add_lift(add_inst(m2, 1, f(Var(2))), 2, 2)), 5);
    ctx = extend(ctx, name("w"), Bool);
    ctx = extend(ctx, name("z"), Bool);
    expr m3 = menv->mk_metavar(ctx);
    lean_assert_eq(fn(m3), 4);
    lean_assert_eq(fn(add_lift(add_inst(m3, 1, f(Var(0))), 1, 1)), 4);
    lean_assert_eq(fn(add_lift(add_inst(m3, 1, f(Var(3))), 1, 1)), 5);
    lean_assert_eq(fn(mk_let("x", Var(0), Var(1))), 1);
    lean_assert_eq(fn(mk_let("x", Var(1), Var(1))), 2);
    lean_assert_eq(fn(mk_let("x", Var(2), Var(1), Var(1))), 3);
    lean_assert_eq(fn(mk_let("x", Var(2), Var(1), Var(4))), 4);
}

static void tst5() {
    metavar_env menv;
    expr m1 = menv->mk_metavar();
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr t = Const("t");
    expr x = Const("x");
    lean_assert(has_free_var(mk_lambda("x", t, f(Var(1))), 0,  menv));
    lean_assert(!has_free_var(mk_lambda("x", t, f(Var(0))), 1, menv));
    lean_assert(!has_free_var(m1, 0, menv));
    lean_assert(!has_free_var(m1, 1, menv));
    context ctx({{"x", Bool}, {"y", Bool}});
    expr m2 = menv->mk_metavar(ctx);
    lean_assert(has_free_var(m2, 0, menv));
    lean_assert(has_free_var(m2, 1, menv));
    lean_assert(!has_free_var(m2, 2, menv));
    lean_assert(has_free_var(Fun({x, Bool}, m2), 0, menv));
    lean_assert(!has_free_var(Fun({x, Bool}, m2), 1, menv));
    lean_assert(has_free_var(Fun({x, Bool}, add_inst(add_lift(m2, 1, 3), 0, Var(0))), 0, menv));
    lean_assert(has_free_var(Fun({x, Bool}, add_inst(add_lift(m2, 1, 1), 0, Var(0))), 0, menv));
    lean_assert(!has_free_var(Fun({x, Bool}, add_inst(add_lift(m2, 1, 1), 0, Var(0))), 1, menv));
    lean_assert(has_free_var(Fun({x, Bool}, add_inst(add_lift(m2, 1, 2), 0, Var(0))), 1, 3, menv));
    lean_assert(!has_free_var(Fun({x, Bool}, add_inst(add_lift(m2, 1, 2), 0, Var(0))), 2, 5, menv));
    lean_assert_eq(lower_free_vars(Fun({x, Bool}, add_inst(add_lift(m2, 1, 2), 0, Var(0))), 5, 3, menv),
                   Fun({x, Bool}, add_inst(add_lift(m2, 1, 2), 0, Var(0))));
    lean_assert_eq(lower_free_vars(Fun({x, Bool}, Var(6)(add_inst(add_lift(m2, 1, 2), 0, Var(0)))), 5, 3, menv),
                   Fun({x, Bool}, Var(3)(add_inst(add_lift(m2, 1, 2), 0, Var(0)))));
}

static void tst6() {
    metavar_env menv;
    expr f  = Const("f");
    expr m1 = menv->mk_metavar();
    expr m2 = menv->mk_metavar(context({{"x", Bool}, {"y", Bool}}));
    lean_assert(lift_free_vars(m1, 0, 1, menv) == m1);
    lean_assert(lift_free_vars(m2, 0, 1, menv) != m2);
    lean_assert(lift_free_vars(m2, 0, 1, menv) == add_lift(m2, 0, 1));
    lean_assert(lift_free_vars(m1, 0, 1) == add_lift(m1, 0, 1));
    lean_assert(lift_free_vars(f(m1), 0, 1, menv) == f(m1));
    lean_assert(lift_free_vars(f(m2), 0, 1, menv) == f(add_lift(m2, 0, 1)));
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    return has_violations() ? 1 : 0;
}

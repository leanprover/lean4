/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <thread>
#include <chrono>
#include "util/test.h"
#include "util/trace.h"
#include "util/exception.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/builtin.h"
#include "kernel/normalizer.h"
#include "library/printer.h"
#include "library/import_all/import_all.h"
#include "library/basic_thms.h"
#include "library/arith/arithlibs.h"
using namespace lean;

expr c(char const * n) { return mk_constant(n); }

static void tst1() {
    environment env;
    expr t0 = Type();
    std::cout << infer_type(t0, env) << "\n";
    lean_assert(infer_type(t0, env) == Type(level()+1));
    expr f = mk_pi("_", t0, t0);
    std::cout << infer_type(f, env) << "\n";
    lean_assert(infer_type(f, env) == Type(level()+1));
    level u = env.add_uvar("u", level() + 1);
    level v = env.add_uvar("v", level() + 1);
    expr g = mk_pi("_", Type(u), Type(v));
    std::cout << infer_type(g, env) << "\n";
    lean_assert(infer_type(g, env) == Type(max(u+1, v+1)));
    std::cout << infer_type(Type(u), env) << "\n";
    lean_assert(infer_type(Type(u), env) == Type(u+1));
    std::cout << infer_type(mk_lambda("x", Type(u), Var(0)), env) << "\n";
    lean_assert(infer_type(mk_lambda("x", Type(u), Var(0)), env) == mk_pi("_", Type(u), Type(u)));
    std::cout << infer_type(mk_lambda("Nat", Type(), mk_lambda("n", Var(0), Var(0))), env) << "\n";
    expr nat = c("nat");
    expr T = Fun("nat", Type(),
             Fun("+", mk_arrow(nat, mk_arrow(nat, nat)),
             Fun("m", nat, mk_app({c("+"), c("m"), c("m")}))));
    std::cout << T << "\n";
    std::cout << infer_type(T, env) << "\n";
    std::cout << Pi("nat", Type(), mk_arrow(mk_arrow(nat, mk_arrow(nat, nat)), mk_arrow(nat, nat))) << "\n";
    lean_assert(infer_type(T, env) == Pi("nat", Type(), mk_arrow(mk_arrow(nat, mk_arrow(nat, nat)), mk_arrow(nat, nat))));
}

static void tst2() {
    try{
        environment env;
        level l1      = env.add_uvar("l1", level() + 1);
        expr t0       = Type();
        expr t1       = Type(l1);
        expr F =
            Fun("Nat", t0,
            Fun("Vec", mk_arrow(c("Nat"), t0),
            Fun("n", c("Nat"),
            Fun("len", mk_arrow(mk_app({c("Vec"), c("n")}), c("Nat")),
            Fun("v", mk_app({c("Vec"), c("n")}),
                mk_app({c("len"), c("v")}))))));
        std::cout << F << "\n";
        std::cout << infer_type(F, env) << "\n";
    }
    catch (exception ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst3() {
    environment env = mk_toplevel();
    expr f = Fun("a", Bool, Eq(Const("a"), True));
    std::cout << infer_type(f, env) << "\n";
    lean_assert(infer_type(f, env) == mk_arrow(Bool, Bool));
    expr t = mk_let("a", expr(), True, Var(0));
    std::cout << infer_type(t, env) << "\n";
}

static void tst4() {
    environment env = mk_toplevel();
    expr a = Eq(iVal(1), iVal(2));
    expr pr   = mk_lambda("x", a, Var(0));
    std::cout << infer_type(pr, env) << "\n";
}

static void tst5() {
    environment env = mk_toplevel();
    env.add_var("P", Bool);
    expr P = Const("P");
    expr H = Const("H");
    unsigned n = 4000;
    expr prop = P;
    expr pr   = H;
    for (unsigned i = 1; i < n; i++) {
        pr   = Conj(P, prop, H, pr);
        prop = And(P, prop);
    }
    expr impPr = Discharge(P, prop, Fun({H, P}, pr));
    expr prop2 = infer_type(impPr, env);
    lean_assert(Implies(P, prop) == prop2);
}

static void tst6() {
    environment env = mk_toplevel();
    expr A = Const("A");
    expr f = Const("f");
    expr x = Const("x");
    expr t = Fun({A, Type()}, Fun({f, mk_arrow(Int, A)}, Fun({x, Int}, f(x, x))));
    try {
        infer_type(t, env);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst7() {
    environment env = mk_toplevel();
    expr A = Const(name{"foo", "bla", "bla", "foo"});
    expr f = Const("f");
    expr x = Const("x");
    expr t = Fun({A, Type()}, Fun({f, mk_arrow(Int, mk_arrow(A, mk_arrow(A, mk_arrow(A, mk_arrow(A, mk_arrow(A, A))))))}, Fun({x, Int}, f(x, x))));
    try {
        infer_type(t, env);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst8() {
    environment env = mk_toplevel();
    env.add_var("P", mk_arrow(Int, mk_arrow(Int, Bool)));
    env.add_var("x", Int);
    expr P = Const("P");
    context c;
    c = extend(c, "P", mk_arrow(Bool, Bool));
    c = extend(c, "P", mk_arrow(Int, Int));
    c = extend(c, "H", Var(1)(True));
    c = extend(c, "x", Bool);
    expr t = P(Const("x"), Var(0));
    try {
        infer_type(t, env, c);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst9() {
    environment env = mk_toplevel();
    env.add_var("P", mk_arrow(Int, mk_arrow(Int, Bool)));
    env.add_var("x", Int);
    expr P = Const("P");
    context c;
    c = extend(c, "P", mk_arrow(Bool, Bool));
    c = extend(c, "P", Bool, Var(0)(True));
    c = extend(c, "H", Var(1)(True));
    c = extend(c, "x", Bool);
    expr t = P(Const("x"), Var(0));
    try {
        infer_type(t, env, c);
        lean_unreachable();
    } catch (exception & ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

static void tst10() {
    environment env = mk_toplevel();
    env.add_var("f", mk_arrow(Int, Int));
    env.add_var("b", Int);
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr t1 = Let({{a, f(b)}, {a, f(a)}}, f(a));
    expr t2 = f(f(f(b)));
    std::cout << t1 << " --> " << normalize(t1, env) << "\n";
    expr prop  = Eq(t1, t2);
    expr proof = Refl(Int, t1);
    env.add_theorem("simp_eq", prop, proof);
    std::cout << env.get_object("simp_eq").get_name() << "\n";
}

static void tst11() {
    environment env = mk_toplevel();
    env.add_var("f", Int >> (Int >> Int));
    env.add_var("a", Int);
    unsigned n = 1000;
    expr f = Const("f");
    expr a = Const("a");
    expr t1 = f(a,a);
    expr b = Const("a");
    expr t2 = f(a,a);
    expr t3 = f(b,b);
    for (unsigned i = 0; i < n; i++) {
        t1 = f(t1,t1);
        t2 = mk_let("x", expr(), t2, f(Var(0), Var(0)));
        t3 = f(t3,t3);
    }
    lean_assert(t1 != t2);
    env.add_theorem("eqs1", Eq(t1,t2), Refl(Int, t1));
    env.add_theorem("eqs2", Eq(t1,t3), Refl(Int, t1));
}

static expr mk_big(unsigned depth) {
    if (depth == 0)
        return Const("a");
    else
        return Const("f")(mk_big(depth - 1), mk_big(depth - 1));
}

static void tst12() {
#ifndef __APPLE__
    expr t = mk_big(18);
    environment env = mk_toplevel();
    env.add_var("f", Int >> (Int >> Int));
    env.add_var("a", Int);
    type_checker checker(env);
    std::chrono::milliseconds dura(100);
    std::thread thread([&]() {
            try {
                std::cout << checker.infer_type(t) << "\n";
                // Remark: if the following code is reached, we
                // should decrease dura.
                lean_unreachable();
            } catch (interrupted & it) {
                std::cout << "interrupted\n";
            }
        });
    std::this_thread::sleep_for(dura);
    checker.interrupt();
    thread.join();
#endif
}

static void tst13() {
    environment env = mk_toplevel();
    env.add_var("f", Type() >> Type());
    expr f = Const("f");
    std::cout << infer_type(f(Bool), env) << "\n";
    std::cout << infer_type(f(Eq(True,False)), env) << "\n";
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    tst11();
    tst12();
    tst13();
    return has_violations() ? 1 : 0;
}

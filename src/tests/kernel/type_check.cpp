/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "type_check.h"
#include "environment.h"
#include "abstract.h"
#include "exception.h"
#include "builtin.h"
#include "arith.h"
#include "trace.h"
#include "test.h"
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
             Fun("+", arrow(nat, arrow(nat, nat)),
             Fun("m", nat, mk_app({c("+"), c("m"), c("m")}))));
    std::cout << T << "\n";
    std::cout << infer_type(T, env) << "\n";
    std::cout << Pi("nat", Type(), arrow(arrow(nat, arrow(nat, nat)), arrow(nat, nat))) << "\n";
    lean_assert(infer_type(T, env) == Pi("nat", Type(), arrow(arrow(nat, arrow(nat, nat)), arrow(nat, nat))));
}

static void tst2() {
    try{
        environment env;
        level l1      = env.add_uvar("l1", level() + 1);
        expr t0       = Type();
        expr t1       = Type(l1);
        expr F =
            Fun("Nat", t0,
            Fun("Vec", arrow(c("Nat"), t0),
            Fun("n", c("Nat"),
            Fun("len", arrow(mk_app({c("Vec"), c("n")}), c("Nat")),
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
    environment env;
    expr f = Fun("a", Bool, Eq(Const("a"), True));
    std::cout << infer_type(f, env) << "\n";
    lean_assert(infer_type(f, env) == arrow(Bool, Bool));
    expr t = mk_let("a", True, Var(0));
    std::cout << infer_type(t, env) << "\n";
}

static void tst4() {
    environment env;
    expr a = Eq(iVal(1), iVal(2));
    expr pr   = mk_lambda("x", a, Var(0));
    std::cout << infer_type(pr, env) << "\n";
}

int main() {
    continue_on_violation(true);
    enable_trace("type_check");
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}

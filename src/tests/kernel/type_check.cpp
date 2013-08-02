/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "type_check.h"
#include "abstract.h"
#include "exception.h"
#include "trace.h"
#include "test.h"
using namespace lean;

expr c(char const * n) { return constant(n); }

static void tst1() {
    environment env;
    expr t0 = type(level());
    std::cout << infer_type(t0, env) << "\n";
    lean_assert(infer_type(t0, env) == type(level()+1));
    expr f = pi("_", t0, t0);
    std::cout << infer_type(f, env) << "\n";
    lean_assert(infer_type(f, env) == type(level()+1));
    level u = env.define_uvar("u", level() + 1);
    level v = env.define_uvar("v", level() + 1);
    expr g = pi("_", type(u), type(v));
    std::cout << infer_type(g, env) << "\n";
    lean_assert(infer_type(g, env) == type(max(u+1, v+1)));
    std::cout << infer_type(type(u), env) << "\n";
    lean_assert(infer_type(type(u), env) == type(u+1));
    std::cout << infer_type(lambda("x", type(u), var(0)), env) << "\n";
    lean_assert(infer_type(lambda("x", type(u), var(0)), env) == pi("_", type(u), type(u)));
    std::cout << infer_type(lambda("Nat", type(level()), lambda("n", var(0), var(0))), env) << "\n";
    expr nat = c("nat");
    expr T = fun("nat", type(level()),
             fun("+", arrow(nat, arrow(nat, nat)),
             fun("m", nat, app(c("+"), c("m"), c("m")))));
    std::cout << T << "\n";
    std::cout << infer_type(T, env) << "\n";
    std::cout << Fun("nat", type(level()), arrow(arrow(nat, arrow(nat, nat)), arrow(nat, nat))) << "\n";
    lean_assert(infer_type(T, env) == Fun("nat", type(level()), arrow(arrow(nat, arrow(nat, nat)), arrow(nat, nat))));
}

static void tst2() {
    try{
        environment env;
        level l1      = env.define_uvar("l1", level() + 1);
        expr t0       = type(level());
        expr t1       = type(l1);
        expr F =
            fun("Nat", t0,
            fun("Vec", arrow(c("Nat"), t0),
            fun("n", c("Nat"),
            fun("len", arrow(app(c("Vec"), c("n")), c("Nat")),
            fun("v", app(c("Vec"), c("n")),
                app(c("len"), c("v")))))));
        std::cout << F << "\n";
        std::cout << infer_type(F, env) << "\n";
    }
    catch (exception ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

int main() {
    continue_on_violation(true);
    enable_trace("type_check");
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "type_check.h"
#include "exception.h"
#include "trace.h"
#include "test.h"
using namespace lean;

static void tst1() {
    environment env;
    expr t0 = type(level());
    std::cout << infer_type(t0, env) << "\n";
    lean_assert(infer_type(t0, env) == type(level()+1));
    expr t1 = pi("_", t0, t0);
    std::cout << infer_type(t1, env) << "\n";
}

static void tst2() {
    try{
        environment env;
        level l1      = env.define_uvar("l1", level() + 1);
        expr t0       = type(level());
        expr t1       = type(l1);
        expr F =
            lambda("Nat", t0,
            lambda("Vec", arrow(var(0), t0),
            lambda("n", var(1),
            lambda("len", arrow(app(var(1), var(0)), var(2)),
            lambda("v", app(var(2), var(1)),
                   app(var(1), var(0)))))));
        std::cout << F << "\n";
        std::cout << infer_type(F, env) << "\n";
    }
    catch (exception ex) {
        std::cout << "Error: " << ex.what() << "\n";
    }
}

int main() {
    // continue_on_violation(true);
    enable_trace("type_check");
    tst1();
    return 0;
    tst2();
    return has_violations() ? 1 : 0;
}

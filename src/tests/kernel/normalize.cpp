/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "normalize.h"
#include "trace.h"
#include "test.h"
using namespace lean;

static void eval(expr const & e) {
    std::cout << e << " --> " << normalize(e) << "\n";
}

static void tst1() {
    expr f = constant("f");
    expr a = constant("a");
    expr b = constant("b");
    expr x = var(0);
    expr y = var(1);
    expr t = prop();
    eval(app(lambda("x", t, x), a));
    eval(app(lambda("x", t, x), a, b));
    eval(lambda("x", t, f(x)));
    eval(lambda("y", t, lambda("x", t, f(y, x))));
    eval(app(lambda("x", t,
                    app(lambda("f", t,
                               app(var(0), b)),
                        lambda("g", t, f(var(1))))),
                 a));
}

int main() {
    enable_trace("normalize");
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

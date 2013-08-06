/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <thread>
#include <mutex>
#include <vector>
#include "expr.h"
#include "max_sharing.h"
#include "free_vars.h"
#include "deep_copy.h"
#include "abstract.h"
#include "normalize.h"
#include "arith.h"
#include "test.h"
using namespace lean;

expr normalize(expr const & e) {
    environment env;
    env.add_var("a", int_type());
    env.add_var("b", int_type());
    env.add_var("f", arrow(int_type(), arrow(int_type(), int_type())));
    env.add_var("h", arrow(int_type(), arrow(int_type(), int_type())));
    return normalize(e, env);
}

static void mk(expr const & a) {
    expr b = constant("b");
    for (unsigned i = 0; i < 100; i++) {
        expr h = constant("h");
        h = h(a);
        for (unsigned j = 0; j < 100; j++)
            h = app(h, b);
        h = max_sharing(h);
        lean_assert(closed(h));
        h = normalize(h);
        h = abstract(h, a);
        lean_assert(!closed(h));
        h = deep_copy(h);
    }
}

static void tst1() {
    expr a = constant("a");
    expr f = constant("f");
    a = f(a, a);
    std::vector<std::thread> ts;

    for (unsigned i = 0; i < 8; i++) {
        ts.push_back(std::thread([&](){ mk(a); }));
    }
    for (unsigned i = 0; i < 8; i++) {
        ts[i].join();
        std::cout << "finished " << i << "\n";
    }
}

int main() {
    tst1();
    return 0;
}

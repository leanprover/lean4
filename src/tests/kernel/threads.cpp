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
    env.add_var("a", Int);
    env.add_var("b", Int);
    env.add_var("f", Int >> (Int >> Int));
    env.add_var("h", Int >> (Int >> Int));
    return normalize(e, env);
}

static void mk(expr const & a) {
    expr b = Const("b");
    for (unsigned i = 0; i < 100; i++) {
        expr h = Const("h");
        h = h(a);
        for (unsigned j = 0; j < 100; j++)
            h = mk_app(h, b);
        h = max_sharing(h);
        lean_assert(closed(h));
        h = normalize(h);
        h = abstract(h, a);
        lean_assert(!closed(h));
        h = deep_copy(h);
    }
}

static void tst1() {
    expr a = Const("a");
    expr f = Const("f");
    a = f(a, a);
    std::vector<std::thread> ts;

    #ifndef __APPLE__
    for (unsigned i = 0; i < 8; i++) {
        ts.push_back(std::thread([&](){ mk(a); }));
    }
    for (unsigned i = 0; i < 8; i++) {
        ts[i].join();
        std::cout << "finished " << i << "\n";
    }
    #endif
}

int main() {
    tst1();
    return 0;
}

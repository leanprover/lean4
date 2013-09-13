/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <thread>
#include <mutex>
#include <vector>
#include "util/test.h"
#include "kernel/expr.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/normalizer.h"
#include "library/max_sharing.h"
#include "library/deep_copy.h"
#include "library/import_all/import_all.h"
#include "library/arith/arith.h"
using namespace lean;

expr norm(expr const & e, environment & env) {
    env.add_var("a", Int);
    env.add_var("b", Int);
    env.add_var("f", Int >> (Int >> Int));
    env.add_var("h", Int >> (Int >> Int));
    return normalize(e, env);
}

static void mk(expr const & a) {
    environment env = mk_toplevel();
    expr b = Const("b");
    for (unsigned i = 0; i < 100; i++) {
        expr h = Const("h");
        h = h(a);
        for (unsigned j = 0; j < 100; j++)
            h = mk_app(h, b);
        h = max_sharing(h);
        lean_assert(closed(h));
        environment env2 = env.mk_child();
        h = norm(h, env2);
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
    #else
    mk(a);
    #endif
}

int main() {
    tst1();
    return 0;
}

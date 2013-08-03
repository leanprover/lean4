/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "expr.h"
#include "abstract.h"
#include "instantiate.h"
#include "deep_copy.h"
#include "name.h"
#include "test.h"
using namespace lean;

expr mk_big(expr f, unsigned depth, unsigned val) {
    if (depth == 1)
        return constant(name(val));
    else
        return f(mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1));
}

static void tst1() {
    expr f = constant("f");
    expr r = mk_big(f, 16, 0);
    expr n = constant(name(0u));
    for (unsigned i = 0; i < 20; i++) {
        r = abstract(n, r);
    }
}

static void tst2() {
    expr r = lambda("x", type(level()), app(var(0), var(1), var(2)));
    std::cout << instantiate_with_closed(constant("a"), r) << std::endl;
    lean_assert(instantiate_with_closed(constant("a"), r) == lambda("x", type(level()), app(var(0), constant("a"), var(1))));
    lean_assert(instantiate_with_closed(constant("b"), instantiate_with_closed(constant("a"), r)) ==
                lambda("x", type(level()), app(var(0), constant("a"), constant("b"))));
    std::cout << instantiate_with_closed(constant("a"), abst_body(r)) << std::endl;
    lean_assert(instantiate_with_closed(constant("a"), abst_body(r)) == app(constant("a"), var(0), var(1)));
    std::cout << instantiate(var(10), r) << std::endl;
    lean_assert(instantiate(var(10), r) == lambda("x", type(level()), app(var(0), var(11), var(1))));
 }

int main() {
    continue_on_violation(true);
    tst1();
    tst2();
    std::cout << "done" << "\n";
    return has_violations() ? 1 : 0;
}

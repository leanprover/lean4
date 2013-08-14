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
        return mk_constant(name(val));
    else
        return f(mk_big(f, depth - 1, val << 1), mk_big(f, depth - 1, (val << 1) + 1));
}

static void tst1() {
    expr f = Const("f");
    expr r = mk_big(f, 16, 0);
    expr n = Const(name(0u));
    for (unsigned i = 0; i < 20; i++) {
        r = abstract(r, n);
    }
}

static void tst2() {
    expr r = mk_lambda("x", Type(), mk_app({Var(0), Var(1), Var(2)}));
    std::cout << instantiate_with_closed(r, Const("a")) << std::endl;
    lean_assert(instantiate_with_closed(r, Const("a")) == mk_lambda("x", Type(), mk_app({Var(0), Const("a"), Var(1)})));
    lean_assert(instantiate_with_closed(instantiate_with_closed(r, Const("a")), Const("b")) ==
                mk_lambda("x", Type(), mk_app({Var(0), Const("a"), Const("b")})));
    std::cout << instantiate_with_closed(abst_body(r), Const("a")) << std::endl;
    lean_assert(instantiate_with_closed(abst_body(r), Const("a")) == mk_app({Const("a"), Var(0), Var(1)}));
    std::cout << instantiate(r, Var(10)) << std::endl;
    lean_assert(instantiate(r, Var(10)) == mk_lambda("x", Type(), mk_app({Var(0), Var(11), Var(1)})));
    std::cout << mk_pi("_", Var(3), Var(4)) << std::endl;
    std::cout << instantiate(mk_pi("_", Var(3), Var(4)), Var(0)) << std::endl;
    lean_assert(instantiate(mk_pi("_", Var(3), Var(4)), Var(0)) == mk_pi("_", Var(2), Var(3)));
}

int main() {
    tst1();
    tst2();
    std::cout << "done" << "\n";
    return has_violations() ? 1 : 0;
}

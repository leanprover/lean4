/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "library/expr_lt.h"
using namespace lean;

static void lt(expr const & e1, expr const & e2, bool expected) {
    lean_assert(is_lt(e1, e2, false) == expected);
    lean_assert(is_lt(e1, e2, false) == !(e1 == e2 || (is_lt(e2, e1, false))));
}

static void tst1() {
    lt(Var(0), Var(0), false);
    lt(Var(0), Var(1), true);
    lt(Const("a"), Const("b"), true);
    lt(Const("a"), Const("a"), false);
    lt(Var(1), Const("a"), true);
    lt(mk_app(Const("f"), Var(0)), mk_app(Const("f"), Var(0), Const("a")), true);
    lt(mk_app(Const("f"), Var(0), Const("a"), Const("b")), mk_app(Const("f"), Var(0), Const("a")), false);
    lt(mk_app(Const("f"), Var(0), Const("a")), mk_app(Const("g"), Var(0), Const("a")), true);
    lt(mk_app(Const("f"), Var(0), Const("a")), mk_app(Const("f"), Var(1), Const("a")), true);
    lt(mk_app(Const("f"), Var(0), Const("a")), mk_app(Const("f"), Var(0), Const("b")), true);
    lt(mk_app(Const("f"), Var(0), Const("a")), mk_app(Const("f"), Var(0), Const("a")), false);
    lt(mk_app(Const("g"), Var(0), Const("a")), mk_app(Const("f"), Var(0), Const("a")), false);
    lt(mk_app(Const("f"), Var(1), Const("a")), mk_app(Const("f"), Var(0), Const("a")), false);
    lt(mk_app(Const("f"), Var(0), Const("b")), mk_app(Const("f"), Var(0), Const("a")), false);
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}

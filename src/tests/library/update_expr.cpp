/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "kernel/update_expr.h"
using namespace lean;

static void tst1() {
    expr a = Const("a");
    expr b = Const("b");
}

static void tst2() {
    expr a  = Const("a");
    expr N  = Const("N");
    expr t1 = Fun(a, N, a);
    expr b  = Const("b");
    expr t2 = update_abstraction(t1, N, abst_body(t1));
    lean_assert(is_eqp(t1, t2));
    t2 = update_abstraction(t1, N, a);
    lean_assert(!is_eqp(t1, t2));
    lean_assert(abst_body(t2) ==  a);
    t1 = Pi(a, N, a);
    t2 = update_abstraction(t1, N, abst_body(t1));
    lean_assert(is_eqp(t1, t2));
}

void tst3() {
    expr a   = Const("a");
    expr b   = Const("b");
    expr f   = Const("f");
    expr t1  = Let(a, b, f(a));
    expr t2  = update_let(t1, none_expr(), b, let_body(t1));
    lean_assert(is_eqp(t1, t2));
    t2  = update_let(t1, none_expr(), a, let_body(t1));
    lean_assert(!is_eqp(t1, t2));
    lean_assert(t2 == Let(a, a, f(a)));
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}

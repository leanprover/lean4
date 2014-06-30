/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr N = Const("N");
    expr x = Local("x", N);
    expr y = Local("y", N);
    expr h = Local("h", N >> (N >> (N >> N)));
    expr a = Const("a");
    expr b = Const("b");
    expr c = Const("c");
    expr d = Const("d");
    expr F1 = Fun(x, x)(f, a);
    lean_assert(is_head_beta(F1));
    lean_assert_eq(head_beta_reduce(F1), f(a));
    expr F2 = Fun({h, y}, h(y))(f, a, b, c);
    lean_assert(is_head_beta(F2));
    lean_assert_eq(head_beta_reduce(F2), f(a, b, c));
    expr F3 = Fun(x, f(Fun(y, y)(x), x))(a);
    lean_assert(is_head_beta(F3));
    lean_assert(head_beta_reduce(F3) == f(Fun(y, y)(a), a));
    lean_assert(beta_reduce(F3) == f(a, a));
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}

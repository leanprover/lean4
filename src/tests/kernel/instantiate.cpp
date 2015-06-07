/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/init_module.h"
#include "util/sexpr/init_module.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/init_module.h"
#include "library/init_module.h"
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
    expr F1 = mk_app(Fun(x, x), f, a);
    lean_assert(is_head_beta(F1));
    lean_assert_eq(head_beta_reduce(F1), mk_app(f, a));
    expr F2 = mk_app(Fun({h, y}, mk_app(h, y)), f, a, b, c);
    lean_assert(is_head_beta(F2));
    lean_assert_eq(head_beta_reduce(F2), mk_app(f, a, b, c));
    expr F3 = mk_app(Fun(x, mk_app(f, mk_app(Fun(y, y), x), x)), a);
    lean_assert(is_head_beta(F3));
    lean_assert(head_beta_reduce(F3) == mk_app(f, mk_app(Fun(y, y), a), a));
}

int main() {
    save_stack_info();
    initialize_util_module();
    initialize_sexpr_module();
    initialize_kernel_module();
    tst1();
    finalize_kernel_module();
    finalize_sexpr_module();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}

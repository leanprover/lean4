/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "library/expr_lt.h"
#include "util/init_module.h"
using namespace lean;

static void lt(expr const & e1, expr const & e2, bool expected) {
    lean_assert(is_lt(e1, e2, false) == expected);
    lean_assert(is_lt(e1, e2, false) == !(e1 == e2 || (is_lt(e2, e1, false))));
}

static void tst1() {
    lt(mk_bvar(0), mk_bvar(0), false);
    lt(mk_bvar(0), mk_bvar(1), true);
    lt(mk_const("a"), mk_const("b"), true);
    lt(mk_const("a"), mk_const("a"), false);
    lt(mk_bvar(1), mk_const("a"), true);
    lt(mk_app(mk_const("f"), mk_bvar(0)), mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), true);
    lt(mk_app(mk_const("f"), mk_bvar(0), mk_const("a"), mk_const("b")), mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), false);
    lt(mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), mk_app(mk_const("g"), mk_bvar(0), mk_const("a")), true);
    lt(mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), mk_app(mk_const("f"), mk_bvar(1), mk_const("a")), true);
    lt(mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), mk_app(mk_const("f"), mk_bvar(0), mk_const("b")), true);
    lt(mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), false);
    lt(mk_app(mk_const("g"), mk_bvar(0), mk_const("a")), mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), false);
    lt(mk_app(mk_const("f"), mk_bvar(1), mk_const("a")), mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), false);
    lt(mk_app(mk_const("f"), mk_bvar(0), mk_const("b")), mk_app(mk_const("f"), mk_bvar(0), mk_const("a")), false);
}

int main() {
    save_stack_info();
    initialize_util_module();
    tst1();
    finalize_util_module();
    return has_violations() ? 1 : 0;
}

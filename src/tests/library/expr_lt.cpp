/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "kernel/kernel.h"
#include "library/expr_lt.h"
#include "library/arith/nat.h"
#include "library/arith/int.h"
#include "library/arith/real.h"
using namespace lean;

static void lt(expr const & e1, expr const & e2, bool expected) {
    lean_assert(is_lt(e1, e2, false) == expected);
    lean_assert(is_lt(e1, e2, false) == !(e1 == e2 || (is_lt(e2, e1, false))));
}

static void tst1() {
    lt(iVal(1), iVal(1), false);
    lt(iVal(1), iVal(2), true);
    lt(rVal(1), rVal(1), false);
    lt(rVal(1), rVal(2), true);
    lt(nVal(1), nVal(1), false);
    lt(nVal(1), nVal(2), true);
    lt(Var(0), Var(0), false);
    lt(Var(0), Var(1), true);
    lt(False, True, true);
    lt(False, False, false);
    lt(Bool, Int, true);
    lt(Const("a"), Const("b"), true);
    lt(Const("a"), Const("a"), false);
    lt(Var(1), Const("a"), true);
    lt(Const("f")(Var(0)), Const("f")(Var(0), Const("a")), true);
    lt(Const("f")(Var(0), Const("a"), Const("b")), Const("f")(Var(0), Const("a")), false);
    lt(Const("f")(Var(0), Const("a")), Const("g")(Var(0), Const("a")), true);
    lt(Const("f")(Var(0), Const("a")), Const("f")(Var(1), Const("a")), true);
    lt(Const("f")(Var(0), Const("a")), Const("f")(Var(0), Const("b")), true);
    lt(Const("f")(Var(0), Const("a")), Const("f")(Var(0), Const("a")), false);
    lt(Const("g")(Var(0), Const("a")), Const("f")(Var(0), Const("a")), false);
    lt(Const("f")(Var(1), Const("a")), Const("f")(Var(0), Const("a")), false);
    lt(Const("f")(Var(0), Const("b")), Const("f")(Var(0), Const("a")), false);
    lt(Type(level()), Type(level()+1), true);
    lt(Type(level("u")), Type(level("z")), true);
    lt(Type(level("u") + 1), Type(level("u") + 2), true);
    lt(Type(level("u") + 1), Type(level("u") + 1), false);
    lt(Type(max({level("u"), level("v")})), Type(max({level("u"), level("z")})), true);
    lt(Type(max({level("u"), level("v")})), Type(max({level("u"), level("v")})), false);
    lt(mk_lambda("x", Int, Var(0)), mk_lambda("y", Real, Var(0)), true);
    lt(mk_lambda("x", Int, Var(0)), mk_lambda("y", Real, Var(10)), true);
    lt(mk_lambda("x", Bool, Var(100)), mk_lambda("y", Real, Var(10)), true);
    lt(mk_lambda("x", Int, Var(0)), mk_lambda("y", Int, Var(0)), false);
    lt(mk_let("x", Int, iVal(10), Var(0)), mk_let("y", Real, rVal(10), Var(0)), true);
    lt(mk_let("x", Int, iVal(10), Var(0)), mk_let("y", Int, iVal(20), Var(0)), true);
    lt(mk_let("x", Int, iVal(10), Var(0)), mk_let("y", Int, iVal(10), Var(1)), true);
    lt(mk_let("x", Int, iVal(10), Var(0)), mk_let("y", Int, iVal(10), Var(0)), false);
    lt(mk_pi("x", Int, Int), mk_pi("y", Real, Bool), true);
    lt(mk_pi("x", Int, Int), mk_pi("y", Int, Real), true);
    lt(mk_pi("x", Int, Int), mk_pi("y", Int, Int), false);
    local_context lctx1{mk_lift(0, 1), mk_inst(0, Const("a"))};
    local_context lctx2{mk_lift(0, 1), mk_inst(0, Const("b"))};
    local_context lctx3{mk_lift(3, 1), mk_inst(0, Const("a"))};
    local_context lctx4{mk_lift(0, 1), mk_inst(0, Const("a")), mk_inst(0, Const("b"))};
    local_context lctx5{mk_inst(0, Const("a")), mk_inst(0, Const("a"))};
    lt(mk_metavar("a", lctx1), mk_metavar("b", lctx1), true);
    lt(mk_metavar("a", lctx1), mk_metavar("a", lctx2), true);
    lt(mk_metavar("a", lctx1), mk_metavar("a", lctx3), true);
    lt(mk_metavar("a", lctx1), mk_metavar("a", lctx4), true);
    lt(mk_metavar("a", lctx1), mk_metavar("a", lctx5), true);
    lt(mk_metavar("a", lctx1), mk_metavar("a", lctx1), false);
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}

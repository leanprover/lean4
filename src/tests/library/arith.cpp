/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/builtin.h"
#include "kernel/normalizer.h"
#include "library/arith/arith.h"
using namespace lean;

static void tst1() {
    environment env;
    normalizer  norm(env);
    import_basic(env);
    import_arith(env);
    env.add_var("n", Nat);
    expr n = Const("n");
    lean_assert_eq(mk_nat_type(), Nat);
    lean_assert_eq(norm(nMul(nVal(2), nVal(3))), nVal(6));
    lean_assert_eq(norm(nLe(nVal(2), nVal(3))), True);
    lean_assert_eq(norm(nLe(nVal(5), nVal(3))), False);
    lean_assert_eq(norm(nLe(nVal(2), nVal(3))), True);
    lean_assert_eq(norm(nLe(n, nVal(3))), nLe(n, nVal(3)));
    env.add_var("x", Real);
    expr x = Const("x");
    lean_assert_eq(mk_real_type(), Real);
    lean_assert_eq(norm(rMul(rVal(2), rVal(3))), rVal(6));
    lean_assert_eq(norm(rDiv(rVal(2), rVal(0))), rVal(0));
    lean_assert_eq(norm(rLe(rVal(2),  rVal(3))), True);
    lean_assert_eq(norm(rLe(rVal(5),  rVal(3))), False);
    lean_assert_eq(norm(rLe(rVal(2),  rVal(3))), True);
    lean_assert_eq(norm(rLe(x, rVal(3))), rLe(x, rVal(3)));
    env.add_var("i", Int);
    expr i = Const("i");
    lean_assert_eq(norm(i2r(i)), i2r(i));
    lean_assert_eq(norm(i2r(iVal(2))), rVal(2));
    lean_assert_eq(mk_int_type(), Int);
    lean_assert_eq(norm(n2i(n)), n2i(n));
    lean_assert_eq(norm(n2i(nVal(2))), iVal(2));
    lean_assert_eq(norm(iDiv(iVal(2), iVal(0))), iVal(0));
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}


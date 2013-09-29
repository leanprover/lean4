/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "util/test.h"
#include "util/numerics/mpq.h"
#include "util/numerics/xnumeral.h"
using namespace lean;

static void inv() {
    mpq x1(214, 6);
    mpq x2(-131, 8);
    xnumeral_kind neg_inf = XN_MINUS_INFINITY;
    xnumeral_kind pos_inf = XN_PLUS_INFINITY;
    inv<mpq>(x1, neg_inf);
    inv<mpq>(x2, pos_inf);
    lean_assert_eq(x1, mpq(0, 1));
    lean_assert_eq(x2, mpq(0, 1));
}
static void div() {
    mpq r1, r2, r3, r4;
    xnumeral_kind rk1, rk2, rk3, rk4;
    mpq x1(214, 6);
    mpq x2(-131, 8);

    // div(T & r, xnumeral_kind & rk, T const & a, xnumeral_kind ak, T const & b, xnumeral_kind bk) {
    div(r1, rk1, x1, XN_NUMERAL,        x2, XN_PLUS_INFINITY);
    lean_assert_eq(r1,  mpq(0, 1));
    lean_assert_eq(rk1, XN_NUMERAL);

    div(r2, rk2, x2, XN_NUMERAL,        x2, XN_MINUS_INFINITY);
    lean_assert_eq(r2, mpq(0, 1));
    lean_assert_eq(rk2, XN_NUMERAL);

    div(r3, rk3, x1, XN_PLUS_INFINITY,  x2, XN_NUMERAL);
    lean_assert_eq(r3, mpq(0, 1));
    lean_assert_eq(rk3, XN_MINUS_INFINITY);

    div(r4, rk4, x2, XN_MINUS_INFINITY, x2, XN_NUMERAL);
    lean_assert_eq(r4, mpq(0, 1));
    lean_assert_eq(rk4, XN_PLUS_INFINITY);
}

static void lt() {
    mpq x1(214, 6);
    mpq x2(-131, 8);
    lean_assert_eq(lt(x1, XN_NUMERAL, x2, XN_MINUS_INFINITY), false);
}

int main() {
    inv();
    div();
    lt();
    return has_violations() ? 1 : 0;
}

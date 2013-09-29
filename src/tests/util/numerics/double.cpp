/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "util/test.h"
#include "util/numerics/double.h"
using namespace lean;

static void abs() {
    double d1 = -398723.3218937912;
    double d2 = -9823.3487729;
    double d3 = 0.0;
    double d4 = 398.347389;
    double d5 = 78398.30912;
    double_abs(d1);
    double_abs(d2);
    double_abs(d3);
    double_abs(d4);
    double_abs(d5);
    lean_assert_eq(d1, 398723.3218937912);
    lean_assert_eq(d2, 9823.3487729);
    lean_assert_eq(d3, 0.0);
    lean_assert_eq(d4, 398.347389);
    lean_assert_eq(d5, 78398.30912);
}

static void ceil() {
    double d1 = -398723.3218937912;
    double d2 = -9823.3487729;
    double d3 = 0.0;
    double d4 = 398.347389;
    double d5 = 78398.30912;
    double_ceil(d1);
    double_ceil(d2);
    double_ceil(d3);
    double_ceil(d4);
    double_ceil(d5);
    lean_assert_eq(d1, -398723);
    lean_assert_eq(d2, -9823);
    lean_assert_eq(d3, 0.0);
    lean_assert_eq(d4, 399);
    lean_assert_eq(d5, 78399);
}

int main() {
    abs();
    ceil();
    return has_violations() ? 1 : 0;
}

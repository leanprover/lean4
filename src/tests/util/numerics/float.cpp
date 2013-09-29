/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include "util/test.h"
#include "util/numerics/float.h"
using namespace lean;

static void abs() {
    float f1 = -398723.3218937912;
    float f2 = -9823.3487729;
    float f3 = 0.0;
    float f4 = 398.347389;
    float f5 = 78398.30912;
    float_abs(f1);
    float_abs(f2);
    float_abs(f3);
    float_abs(f4);
    float_abs(f5);
    lean_assert_eq(f1, 398723.3218937912f);
    lean_assert_eq(f2, 9823.3487729f);
    lean_assert_eq(f3, 0.0f);
    lean_assert_eq(f4, 398.347389f);
    lean_assert_eq(f5, 78398.30912f);
}

static void ceil() {
    float f1 = -398723.3218937912;
    float f2 = -9823.3487729;
    float f3 = 0.0;
    float f4 = 398.347389;
    float f5 = 78398.30912;
    float_ceil(f1);
    float_ceil(f2);
    float_ceil(f3);
    float_ceil(f4);
    float_ceil(f5);
    lean_assert_eq(f1, -398723);
    lean_assert_eq(f2, -9823);
    lean_assert_eq(f3, 0.0);
    lean_assert_eq(f4, 399);
    lean_assert_eq(f5, 78399);
}

int main() {
    abs();
    ceil();
    return has_violations() ? 1 : 0;
}

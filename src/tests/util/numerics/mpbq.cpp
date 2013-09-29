/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#include <iostream>
#include <sstream>
#include "util/test.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/mpq.h"
using namespace lean;

static void tst1() {
    mpbq a(1, 1);
    std::cout << a << "\n";
    lean_assert_eq(a, mpq(1, 2));
    std::cout << mpbq(mpq(1, 3)) << "\n";
    lean_assert(!set(a, mpq(1, 3)));
    lean_assert_eq(a, mpbq(1, 2));
    mpq b;
    b = a;
    lean_assert_eq(b, mpq(1, 4));
    lean_assert_eq(inv(b), 4);
    lean_assert_eq(a/2, mpbq(1, 3));
    lean_assert_eq(a/1, a);
    lean_assert_eq(a/8, mpbq(1, 5));
    lean_assert_eq(3*a/8, mpbq(3, 5));
    mpbq l(0), u(1);
    mpq v(21, 91);
    while (true) {
        lean_assert_lt(l, v);
        lean_assert_lt(v, u);
        std::cout << mpbq::decimal(l, 20) << " " << v << " " << mpbq::decimal(u, 20) << "\n";
        if (lt_1div2k((u - l)/2, 50))
            break;
        refine_lower(v, l, u);
        refine_upper(v, l, u);
    }
}

static void tst2() {
    mpbq num(2);
    std::ostringstream out;
    out << num;
    lean_assert_eq(out.str(), "2");
    mpbq a(-1, 2);
    std::ostringstream out2;
    display_decimal(out2, a, 10);
    lean_assert_eq(out2.str(), "-0.25");
    lean_assert(lt_1div2k(a, 8));
    mul2(a);
    lean_assert_eq(a, mpbq(-1, 1));
    mul2k(a, 3);
    lean_assert_eq(a, mpbq(-4));
    mul2k(a, 0);
    lean_assert_eq(a, mpbq(-4));
    mul2k(a, 2);
    lean_assert_eq(a, mpbq(-16));
    lean_assert_eq(cmp(mpbq(1, 2), mpbq(1, 4)), 1);
    lean_assert_eq(cmp(mpbq(1, 2), mpbq(1, 2)), 0);
    lean_assert_eq(cmp(mpbq(1, 2), mpbq(3, 2)), -1);
    lean_assert_eq(cmp(mpbq(3, 2), mpbq(3, 4)), 1);
    lean_assert_eq(cmp(mpbq(15, 2), mpbq(3, 1)), 1);
    lean_assert_eq(cmp(mpbq(7, 1), mpz(3)), 1);
    lean_assert_eq(cmp(mpbq(3, 0), mpz(3)), 0);
    lean_assert_eq(cmp(mpbq(2, 0), mpz(3)), -1);
    lean_assert_eq(cmp(mpbq(7, 4), mpz(10)), -1);
    lean_assert_eq(mpbq(0, 1), mpz(0));
    set(a, mpq(1, 4));
    lean_assert_eq(cmp(a, mpbq(1, 2)), 0);
    set(a, mpq(0));
    lean_assert(a.is_zero());
    a += 3u;
    lean_assert_eq(a, 3);
    a += -2;
    lean_assert_eq(a, 1);
    div2k(a, 2);
    lean_assert_eq(a, mpq(1, 4));
    a += 3u;
    lean_assert_eq(a, mpq(13, 4));
    a += -2;
    lean_assert_eq(a, mpq(5, 4));
    a -= 1u;
    lean_assert_eq(a, mpq(1, 4));
    a -= -2;
    lean_assert_eq(a, mpq(9, 4));
}

static void tst3() {
    mpbq x1(256, 4);
    mpq  x2(32, 2);
    mpbq x3(1, 4);
    mpbq x4(3, 8);
    mpbq x5(3, 0);
    mpbq x6(3, 2);
    mpbq x7(4, 3);
    lean_assert_eq(x1, 256 / (2 * 2 * 2 * 2));
    lean_assert_eq(x1, x2);
    x3-=x4;
    lean_assert_eq(x3, mpbq(13, 8));
    x5-=2;
    lean_assert_eq(x5, mpbq(1, 0));
    x6*=x7;
    lean_assert_eq(x6, mpbq(3, 3));
}

static void tst4() {
    mpbq x1(256, 4);
    mpq  x2(32, 2);
    mpbq x3(1, 4);
    mpbq x4(3, 8);
    mpbq x5(3, 0);
    x1*=3u;
    lean_assert_eq(x1, mpbq(48, 0));
    x1*=2;
    lean_assert_eq(x1, mpbq(96, 0));
    x2*=-2;
    lean_assert_eq(x2, mpbq(-32, 0));
    power(x3, x4, 2); // x3 = (3/2^8)^2 = (9/2^16)
    lean_assert_eq(x3, mpbq(9, 16));
    power(x4, x5, 3); // x4 = 3^3 = 27
    lean_assert_eq(x4, mpbq(27, 0));
}

static void tst5() {
    mpbq x1(34, 4);
    mpbq x2(3932, 11);
    mpbq x3(-68, 9);
    mpbq x4(-69048, 15);
    mpbq x5(34, -4);
    mpbq x6(3932, -11);
    mpbq x7(-68, -9);
    mpbq x8(-69048, -15);
    mpbq x9(0, 4);
    lean_assert_eq(x1.magnitude_lb(), 1);
    lean_assert_eq(x2.magnitude_lb(), 0);
    lean_assert_eq(x3.magnitude_lb(), -2);
    lean_assert_eq(x4.magnitude_lb(), 2);
    lean_assert_eq(x5.magnitude_lb(), 9);
    lean_assert_eq(x6.magnitude_lb(), 22);
    lean_assert_eq(x7.magnitude_lb(), 16);
    lean_assert_eq(x8.magnitude_lb(), 32);
    lean_assert_eq(x9.magnitude_lb(), 0);
}

static void tst6() {
    mpbq x1(34, 4);
    mpbq x2(3932, 11);
    mpbq x3(-68, 9);
    mpbq x4(-69048, 15);
    mpbq x5(34, -4);
    mpbq x6(3932, -11);
    mpbq x7(-68, -9);
    mpbq x8(-69048, -15);
    mpbq x9(0, 4);
    lean_assert_eq(x1.magnitude_ub(), x1.magnitude_lb() + 1);
    lean_assert_eq(x2.magnitude_ub(), x2.magnitude_lb() + 1);
    lean_assert_eq(x3.magnitude_ub(), x3.magnitude_lb() - 1);
    lean_assert_eq(x4.magnitude_ub(), x4.magnitude_lb() - 1);
    lean_assert_eq(x5.magnitude_ub(), x5.magnitude_lb() + 1);
    lean_assert_eq(x6.magnitude_ub(), x6.magnitude_lb() + 1);
    lean_assert_eq(x7.magnitude_ub(), x7.magnitude_lb() - 1);
    lean_assert_eq(x8.magnitude_ub(), x8.magnitude_lb() - 1);
    lean_assert_eq(x9.magnitude_ub(), x9.magnitude_lb());
}

static void tst7() {
    mpbq x1(34, 5);
    mpbq x2(21, 0);
    mpbq x3(-68, 4);
    mpbq x4(-67, 8);
    mul2(x1);
    mul2(x2);
    mul2(x3);
    mul2k(x4, 3);
    lean_assert_eq(x1, mpbq(17, 3));
    lean_assert_eq(x2, mpbq(42, 0));
    lean_assert_eq(x3, mpbq(-17, 1));
    lean_assert_eq(x4, mpbq(-67, 5));
}

static void tst8() {
    mpbq x1(36, 4);
    mpbq x2(3932, 11);
    mpbq x3(-68, 9);
    mpbq x4(-69048, 15);
    mpbq x5(0, 4);
    mpbq x6(74, 5);
    mpbq n1;
    mpbq n2;
    mpbq n3;
    mpbq n4;
    mpbq n5;
    mpbq n6;
    lean_assert_eq(root_lower(n1, x1, 2), true);
    lean_assert_eq(n1, mpbq(3, 1));
    lean_assert_eq(root_lower(n2, x2, 3), false);
    lean_assert_eq(n2, mpbq(1, 0));
    lean_assert_eq(root_lower(n3, x3, 3), false);
    lean_assert_eq(n3, mpbq(-3, 2));
    lean_assert_eq(root_lower(n4, x4, 3), false);
    lean_assert_eq(n4, mpbq(-21, 4));
    lean_assert_eq(root_lower(n5, x5, 3), true);
    lean_assert_eq(n5, mpbq(0, 0));
    lean_assert_eq(root_lower(n6, x6, 3), false);
    lean_assert_eq(n6, mpbq(1, 1));
}

static void tst9() {
    mpbq x1(36, 4);
    mpbq x2(3932, 11);
    mpbq x3(-68, 9);
    mpbq x4(-69048, 15);
    mpbq x5(0, 4);
    mpbq x6(74, 5);
    mpbq n1;
    mpbq n2;
    mpbq n3;
    mpbq n4;
    mpbq n5;
    mpbq n6;
    lean_assert_eq(root_upper(n1, x1, 2), true);
    lean_assert_eq(n1, mpbq(3, 1));
    lean_assert_eq(root_upper(n2, x2, 3), false);
    lean_assert_eq(n2, mpbq(9, 3));
    lean_assert_eq(root_upper(n3, x3, 3), false);
    lean_assert_eq(n3, mpbq(-1, 2));
    lean_assert_eq(root_upper(n4, x4, 3), false);
    lean_assert_eq(n4, mpbq(-5, 2));
    lean_assert_eq(root_upper(n5, x5, 3), true);
    lean_assert_eq(n5, mpbq(0, 0));
    lean_assert_eq(root_upper(n6, x6, 3), false);
    lean_assert_eq(n6, mpbq(3, 1));
}

static void tst10() {
    mpbq b(4, 5);
    b.neg();
    lean_assert_eq(b, mpbq(-4, 5));
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    tst8();
    tst9();
    tst10();
    return has_violations() ? 1 : 0;
}

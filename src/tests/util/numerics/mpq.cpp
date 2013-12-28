/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include "util/test.h"
#include "util/serializer.h"
#include "util/numerics/mpq.h"
using namespace lean;

static void tst0() {
    lean::mpq n1("10000000000000000000000000000000000000000");
    lean::mpq n2(317, 511);
    std::cout << n1*n2 << "\n";
}

static void tst1() {
    mpq a(2, 3), b(4, 3);
    b = a / b;
    lean_assert(b == mpq(1, 2));
    a = mpq(2);
    a.inv();
    lean_assert(a == b);
    a = -2;
    b = mpq(-1, 2);
    a.inv();
    lean_assert(a == b);
}

static void tst2() {
    mpq a(2, 3);
    lean_assert(floor(a) == 0);
    lean_assert(ceil(a) == 1);
    mpq b(-2, 3);
    lean_assert(floor(b) == -1);
    lean_assert(ceil(b) == 0);
    mpq c;
    lean_assert(floor(c) == 0);
    lean_assert(ceil(c) == 0);
    mpq d(3);
    lean_assert(d > 0);
    lean_assert(d.is_pos());
    lean_assert(floor(d) == d);
    lean_assert(ceil(d) == d);
    mpq e(-3);
    lean_assert(e < 0);
    lean_assert(e.is_neg());
    lean_assert(floor(e) == e);
    lean_assert(ceil(e) == e);
}

static void tst3() {
    mpq a("1");
    mpq b(1);
    lean_assert(a == b);
}

static void tst4() {
    mpq a(8, 6);
    lean_assert(a == mpq(4, 3));
    lean_assert(mpq(1, 2)+mpq(1, 2) == mpq(1));
    lean_assert(mpq("1/2") < mpq("2/3"));
    lean_assert(mpq(-1, 2).is_neg());
    lean_assert(mpq(-1, 2).is_nonpos());
    lean_assert(!mpq(-1, 2).is_zero());
    lean_assert(mpq(1, 2) > mpq());
    lean_assert(mpq().is_zero());
    lean_assert(mpq(2, 3) + mpq(4, 3) == mpq(2));
    lean_assert(mpq(1, 2) >= mpq(1, 3));
    lean_assert(mpq(3, 4).get_denominator() == 4);
    lean_assert(mpq(3, 4).get_numerator() == 3);
    lean_assert(mpq(1, 2) / mpq(5, 4) == mpq(2, 5));
    lean_assert(mpq(1, 2) - mpq(2, 3) == mpq(-1, 6));
    lean_assert(mpq(3, 4) * mpq(2, 3) == mpq(1, 2));
    a *= 3;
    lean_assert(a == 4);
    a /= 2;
    lean_assert(a == 2);
    lean_assert(a.is_integer());
    a /= 5;
    lean_assert(a == mpq(2, 5));
    lean_assert(!a.is_integer());
    mpq b(3, 7);
    a *= b;
    lean_assert(a == mpq(6, 35));
    a /= b;
    lean_assert(a == mpq(2, 5));
    mpz c(5);
    a *= c;
    lean_assert(a == 2);
    a += c;
    lean_assert(a == 7);
    a -= c;
    lean_assert(a == 2);
    a /= c;
    lean_assert(a == mpq(2, 5));
}

static void tst5() {
    mpq a;
    a = 1;
    lean_assert(a == mpq(1));
    lean_assert(a <= 1);
    lean_assert(a < 2);
    lean_assert(a > 0);
    lean_assert(a >= 0);
    lean_assert(a >= 1);
    lean_assert(!(a >= 2));
    lean_assert(a == 1);
    lean_assert(1 == a);
    lean_assert(a != 2);
    lean_assert(!(a == 3));
    lean_assert(a < mpz(2));
    lean_assert(a <= mpz(1));
    lean_assert(a > 0);
    lean_assert(a <= 1u);
    lean_assert(a < 2u);
    lean_assert(a > 0u);
    lean_assert(a >= 1u);
    lean_assert(a == 1u);
    lean_assert(1u >= a);
    lean_assert(2u > a);
    a = "1/3";
    lean_assert(a == mpq(1, 3));
    a = 2.0;
    lean_assert(a == mpq(2));
    a = mpz(10);
    lean_assert(a == mpq(10));
    lean_assert(a >= mpz(10));
    lean_assert(mpz(10) <= a);
    lean_assert(mpz(10) >= a);
    lean_assert(mpz(10) == a);
}

static void check_dec(mpq const & q, char const * expected, unsigned prec = 10) {
    std::ostringstream s;
    display_decimal(s, q, prec);
    std::cout << s.str() << "\n";
    lean_assert(s.str() == expected);
}

static void tst6() {
    mpq v1(1);
    v1.floor();
    lean_assert(v1 == 1);
    v1.ceil();
    lean_assert(v1 == 1);
    v1 = mpq(1, 2);
    v1.floor();
    lean_assert(v1 == 0);
    v1 = mpq(1, 2);
    v1.ceil();
    lean_assert(v1 == 1);
    v1 -= 2u;
    lean_assert(v1 == -1);
    v1 = mpq(-1, 2);
    v1.floor();
    lean_assert(v1 == -1);
    v1 = mpq(-1, 2);
    v1.ceil();
    lean_assert(v1 == 0);
    check_dec(mpq(-1, 2), "-0.5");
    check_dec(mpq(1, 3),  "0.33333?", 5);
    check_dec(mpq(3),    "3");
    check_dec(mpq(-2, 1), "-2");
    check_dec(mpq(-1, 3),  "-0.33333?", 5);
    check_dec(mpq(-1, 7),  "-0.14285?", 5);

    lean_assert(cmp(mpq(1, 2), mpz(1)) < 0);
    lean_assert(cmp(mpq(3, 2), mpz(1)) > 0);
    lean_assert(cmp(mpq(-3, 2), mpz(-1)) < 0);
}

static void tst7() {
    std::ostringstream out;
    serializer s(out);
    mpq n1("-100000000000000000000000000000000000/3");
    lean_assert(n1.is_neg());
    mpq n2("-3/4");
    mpq n3("1200/2131");
    mpq n4("321/345");
    mpq n5(1, 3);
    s << n1 << n2 << n3 << n4 << n5;
    std::istringstream in(out.str());
    deserializer d(in);
    mpq m1, m2, m3, m4, m5;
    d >> m1 >> m2 >> m3 >> m4 >> m5;
    lean_assert(n1 == m1);
    lean_assert(n2 == m2);
    lean_assert(n3 == m3);
    lean_assert(n4 == m4);
    lean_assert(n5 == m5);
}

int main() {
    tst0();
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    tst6();
    tst7();
    return has_violations() ? 1 : 0;
}

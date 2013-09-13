/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include "util/test.h"
#include "util/numerics/mpbq.h"
#include "util/numerics/mpq.h"
using namespace lean;

static void tst1() {
    mpbq a(1,1);
    std::cout << a << "\n";
    lean_assert(a == mpq(1,2));
    std::cout << mpbq(mpq(1,3)) << "\n";
    lean_assert(!set(a, mpq(1,3)));
    lean_assert(a == mpbq(1,2));
    mpq b;
    b = a;
    lean_assert(b == mpq(1,4));
    lean_assert(inv(b) == 4);
    lean_assert(a/2 == mpbq(1,3));
    lean_assert(a/1 == a);
    lean_assert(a/8 == mpbq(1,5));
    lean_assert((3*a)/8 == mpbq(3,5));
    mpbq l(0), u(1);
    mpq v(1,3);
    while (true) {
        lean_assert(l < v);
        lean_assert(v < u);
        std::cout << mpbq::decimal(l,20) << " " << v << " " << mpbq::decimal(u, 20) << "\n";
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
    lean_assert(out.str() == "2");
    mpbq a(-1,2);
    std::ostringstream out2;
    display_decimal(out2, a, 10);
    lean_assert(out2.str() == "-0.25");
    lean_assert(lt_1div2k(a, 8));
    mul2(a);
    lean_assert(a == mpbq(-1,1));
    mul2k(a, 3);
    lean_assert(a == mpbq(-4));
    mul2k(a, 0);
    lean_assert(a == mpbq(-4));
    mul2k(a, 2);
    lean_assert(a == mpbq(-16));
    lean_assert(cmp(mpbq(1,2), mpbq(1,4)) == 1);
    lean_assert(cmp(mpbq(1,2), mpbq(1,2)) == 0);
    lean_assert(cmp(mpbq(1,2), mpbq(3,2)) == -1);
    lean_assert(cmp(mpbq(3,2), mpbq(3,4)) == 1);
    lean_assert(cmp(mpbq(15,2), mpbq(3,1)) == 1);
    lean_assert(cmp(mpbq(7,1), mpz(3)) == 1);
    lean_assert(cmp(mpbq(3,0), mpz(3)) == 0);
    lean_assert(cmp(mpbq(2,0), mpz(3)) == -1);
    lean_assert(cmp(mpbq(7,4), mpz(10)) == -1);
    lean_assert(mpbq(0,1) == mpz(0));
    set(a, mpq(1,4));
    lean_assert(cmp(a, mpbq(1,2)) == 0);
    set(a, mpq(0));
    lean_assert(a.is_zero());
    a += 3u;
    lean_assert(a == 3);
    a += -2;
    lean_assert(a == 1);
    div2k(a, 2);
    lean_assert(a == mpq(1,4));
    a += 3u;
    lean_assert(a == mpq(13,4));
    a += -2;
    lean_assert(a == mpq(5,4));
    a -= 1u;
    lean_assert(a == mpq(1,4));
    a -= -2;
    lean_assert(a == mpq(9,4));
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

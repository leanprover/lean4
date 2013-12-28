/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <sstream>
#include <string>
#include "util/test.h"
#include "util/serializer.h"
#include "util/numerics/mpz.h"
using namespace lean;

static void tst1() {
    mpz a(-10);
    lean_assert_eq(a.log2(), 0);
    lean_assert_eq(a.mlog2(), 3);
    lean_assert_eq(a.is_power_of_two(), false);
    unsigned shift = 0;
    lean_assert_eq(a.is_power_of_two(shift), false);
    lean_assert_eq(mpz(10).mlog2(), 0);
    mpz r;
    mpz b(30);
    b-=10u;
    lean_assert_eq(b, mpz(20));
    lean_assert(root(r, mpz(4), 2));
    lean_assert_eq(r, 2);
    lean_assert(!root(r, mpz(10), 2));
    lean_assert_eq(r, 3);
    lean_assert_eq(mpz(10) % mpz(3), mpz(1));
    lean_assert_eq(mpz(10) % mpz(-3), 1);
    lean_assert_eq(mpz(-10) % mpz(-3), 2);
    lean_assert_eq(mpz(-10) % mpz(3), 2);
    mpz big;
    big = pow(mpz(10), 10000);
    std::ostringstream out;
    out << big;
    std::string s = out.str();
    lean_assert_eq(s.size(), 10001);
    lean_assert_eq(s[0], '1');
    for (unsigned i = 1; i < 10001; i++) {
        lean_assert_eq(s[i], '0');
    }
}

static void tst2() {
    std::ostringstream out;
    serializer s(out);
    mpz n1("-100000000000000000000000000000000000");
    lean_assert(n1.is_neg());
    mpz n2("0");
    mpz n3("1200");
    mpz n4("321");
    s << n1 << n2 << n3 << n4;
    std::istringstream in(out.str());
    deserializer d(in);
    mpz m1, m2, m3, m4;
    d >> m1 >> m2 >> m3 >> m4;
    lean_assert(n1 == m1);
    lean_assert(n2 == m2);
    lean_assert(n3 == m3);
    lean_assert(n4 == m4);
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

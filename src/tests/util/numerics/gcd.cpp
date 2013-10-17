/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <random>
#include "util/test.h"
#include "util/numerics/gcd.h"
#include "util/numerics/mpz.h"
using namespace lean;

static void tst1(unsigned num_tests, unsigned max_val) {
    std::mt19937 rng;
    std::uniform_int_distribution<unsigned int> uint_dist;
    for (unsigned i = 0; i < num_tests; i++) {
        int val1;
        int val2;
        do {
            val1 = uint_dist(rng) % max_val;
            val2 = uint_dist(rng) % max_val;
        } while (val1 == 0 || val2 == 0 || val1 == val2);
        int g, a, b;
        gcdext(g, a, b, val1, val2);
        mpz _g, _a, _b;
        gcdext(_g, _a, _b, mpz(val1), mpz(val2));
        lean_assert_eq(_g.get_int(), g);
        lean_assert_eq(_a.get_int(), a);
        lean_assert_eq(_b.get_int(), b);
    }
}

int main() {
    tst1(1000,    10);
    tst1(1000,    100);
    tst1(10000,   1000);
    tst1(10000,   100);
    tst1(10000,   1000);
    tst1(1000000, 10000);
    return has_violations() ? 1 : 0;
}

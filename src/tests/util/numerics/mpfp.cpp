/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Soonho Kong
*/
#include <iostream>
#include "util/test.h"
#include "util/numerics/mpfp.h"
using namespace lean;

static void tst1() {
    mpfp a(3.141592, 64);
    std::cout << "a            = |" << a << "|" << std::endl;
    std::cout << "exp(a, UP  ) = |" << exp(a, MPFR_RNDU) << "|" << std::endl;
    std::cout << "exp(a, NEAR) = |" << exp(a, MPFR_RNDN) << "|" << std::endl;
    std::cout << "exp(a, DOWN) = |" << exp(a, MPFR_RNDD) << "|" << std::endl;

    mpfp b = mpfp(5.141592, 128);
    std::cout << "b            = |" << b << "|" << std::endl;
    std::cout << "exp(b, UP  ) = |" << exp(b, MPFR_RNDU) << "|" << std::endl;
    std::cout << "exp(b, NEBR) = |" << exp(b, MPFR_RNDN) << "|" << std::endl;
    std::cout << "exp(b, DOWN) = |" << exp(b, MPFR_RNDD) << "|" << std::endl;

    mpfp c = mpfp(6.141592, 256);
    std::cout << "c            = |" << c << "|" << std::endl;
    std::cout << "exp(c, UP  ) = |" << exp(c, MPFR_RNDU) << "|" << std::endl;
    std::cout << "exp(c, NEAR) = |" << exp(c, MPFR_RNDN) << "|" << std::endl;
    std::cout << "exp(c, DOWN) = |" << exp(c, MPFR_RNDD) << "|" << std::endl;

    std::cout << "a            = |" << a << "|" << std::endl;
    std::cout << "exp(a, UP  ) = |" << exp(a, MPFR_RNDU) << "|" << std::endl;
    std::cout << "exp(a, NEAR) = |" << exp(a, MPFR_RNDN) << "|" << std::endl;
    std::cout << "exp(a, DOWN) = |" << exp(a, MPFR_RNDD) << "|" << std::endl;

    std::cout << "b            = |" << b << "|" << std::endl;
    std::cout << "exp(b, UP  ) = |" << exp(b, MPFR_RNDU) << "|" << std::endl;
    std::cout << "exp(b, NEAR) = |" << exp(b, MPFR_RNDN) << "|" << std::endl;
    std::cout << "exp(b, DOWN) = |" << exp(b, MPFR_RNDD) << "|" << std::endl;

    mpfp d = mpfp(6.141592, 512);
    std::cout << "d            = |" << d << "|" << std::endl;
    std::cout << "exp(d, UP  ) = |" << exp(d, MPFR_RNDU) << "|" << std::endl;
    std::cout << "exp(d, NEAR) = |" << exp(d, MPFR_RNDN) << "|" << std::endl;
    std::cout << "exp(d, DOWN) = |" << exp(d, MPFR_RNDD) << "|" << std::endl;
}

static void tst2() {
    mpfp a(10.0, 64);
    mpfp b(10.0, 128);
    lean_assert(a == b);
    for (unsigned i = 16; i < 256; i++) {
        for (unsigned j = 16; j < 256; j++) {
            lean_assert_eq(mpfp(0.0, i), mpfp(0.0, j));
        }
    }
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

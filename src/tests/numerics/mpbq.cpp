/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "test.h"
#include "mpbq.h"
#include "mpq.h"
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

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;

}

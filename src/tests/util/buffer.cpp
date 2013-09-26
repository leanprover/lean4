/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "util/buffer.h"
using namespace lean;

template<typename C>
static void loop(int n) {
    C b;
    b.push_back(n);
    lean_assert(b.size() == 1);
    lean_assert(b.back() == n);
    lean_assert(b[0] == n);
    if (n > 0)
        loop<C>(n-1);
}

static void tst1() {
    buffer<int> b1;
    buffer<int> b2;
    b1.push_back(10);
    lean_assert(b1 != b2);
    b2.push_back(20);
    lean_assert(b1 != b2);
    b2.pop_back();
    b2.push_back(10);
    lean_assert(b1 == b2);
    b2.push_back(20);
    b2.push_back(20);
    lean_assert(b1 != b2);
    b2.shrink(1);
    lean_assert(b1 == b2);
    b2.push_back(100);
    lean_assert(b1 != b2);
    b2 = b1;
    lean_assert(b1 == b2);
    buffer<int> b3(b1);
    lean_assert(b3 == b1);
    lean_assert(b1.back() == 10);
}

int main() {
    loop<buffer<int>>(100);
    tst1();
    return has_violations() ? 1 : 0;
}

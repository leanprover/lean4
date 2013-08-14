/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "buffer.h"
#include "test.h"
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

void perftest() {
    for (unsigned i = 0; i < 10000; i++)
        loop<buffer<int>>(10000);
//    for (unsigned i = 0; i < 10000; i++)
//        loop<std::vector<int>>(10000);
}

int main() {
    loop<buffer<int>>(100);
    return has_violations() ? 1 : 0;
}

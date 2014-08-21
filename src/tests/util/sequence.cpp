/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sequence.h"
#include "util/test.h"
using namespace lean;

namespace lean {
template class sequence<int>;
}

static void tst1() {
    sequence<int> l1;
    lean_assert(!l1);
    sequence<int> l2(10);
    lean_assert(l2);
    lean_assert(is_eqp(l2, l1 + l2));
    lean_assert(is_eqp(l2, l2 + l1));
    lean_assert(!is_eqp(l2, l2 + l2));
    sequence<int> l3(20);
    sequence<int> l4(5);
    sequence<int> r = l4 + (l2 + l2) + (l3 + l4) + sequence<int>(3);
    buffer<int> b;
    r.linearize(b);
    for (auto v : b) std::cout << v << " "; std::cout << "\n";
    lean_assert(b[0] == 5 && b[1] == 10 && b[2] == 10 && b[3] == 20 && b[4] == 5 && b[5] == 3);
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

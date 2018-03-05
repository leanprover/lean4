/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/bit_tricks.h"
using namespace lean;

static void tst1() {
    lean_assert(log2(255u) == 7);
    lean_assert(log2(256u) == 8);
    lean_assert(log2(257u) == 8);
    lean_assert(log2(321u) == 8);
    lean_assert(log2(520u) == 9);
    lean_assert(log2(65535u) == 15);
    lean_assert(log2(65536u) == 16);
    lean_assert(log2(65537u) == 16);
    lean_assert(log2(5203939u) == 22);
    lean_assert(log2(10309482u) == 23);
    lean_assert(log2(41039392u) == 25);
    lean_assert(log2(213469392u) == 27);
    lean_assert(log2(1293828727u) == 30);
    lean_assert(log2(1073741824u) == 30);
    lean_assert(log2(2147483648u) == 31);
    lean_assert(log2(4294967295u) == 31);
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

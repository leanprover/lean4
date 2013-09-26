/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/bit_tricks.h"
using namespace lean;

static void tst1() {
    lean_assert(log2(255) == 7);
    lean_assert(log2(256) == 8);
    lean_assert(log2(257) == 8);
    lean_assert(log2(321) == 8);
    lean_assert(log2(520) == 9);
    lean_assert(log2(65535) == 15);
    lean_assert(log2(65536) == 16);
    lean_assert(log2(65537) == 16);
    lean_assert(log2(5203939) == 22);
    lean_assert(log2(10309482) == 23);
    lean_assert(log2(41039392) == 25);
    lean_assert(log2(213469392) == 27);
    lean_assert(log2(1293828727) == 30);
    lean_assert(log2(1073741824) == 30);
    lean_assert(log2(2147483648u) == 31);
    lean_assert(log2(4294967295u) == 31);
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "util/hash.h"
using namespace lean;

static void tst1() {
    int a[] = {0, 1, 2};
    unsigned h3 = hash(3, [&](unsigned i) { return a[i]; });
    lean_assert(h3 == hash(3, [&](unsigned i) { return a[i]; }));
    unsigned h1 = hash(1, [&](unsigned i) { return a[i]; });
    lean_assert(h1 != h3);
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

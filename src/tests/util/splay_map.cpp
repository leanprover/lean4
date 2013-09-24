/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "util/test.h"
#include "util/splay_map.h"
#include "util/name.h"
using namespace lean;

struct int_cmp { int operator()(int i1, int i2) const { return i1 < i2 ? -1 : (i1 > i2 ? 1 : 0); } };

typedef splay_map<int, name, int_cmp> int2name;

static void tst0() {
    int2name m1;
    m1[10] = name("t1");
    m1[20] = name("t2");
    int2name m2(m1);
    m2[10] = name("t3");
    lean_assert(m1[10] == name("t1"));
    lean_assert(m1[20] == name("t2"));
    lean_assert(m2[10] == name("t3"));
    lean_assert(m2[20] == name("t2"));
}

int main() {
    tst0();
    return has_violations() ? 1 : 0;
}

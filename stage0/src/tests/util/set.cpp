/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <set>
#include "util/test.h"
using namespace lean;

static void tst1() {
    std::set<int*> s;
    int a;
    int b;
    int c;
    a = 10;
    b = 20;
    c = 5;
    s.insert(&a);
    s.insert(&b);
    lean_assert(s.size() == 2);
    s.insert(&a);
    lean_assert(s.size() == 2);
    s.insert(&c);
    lean_assert(s.size() == 3);
    for (int * v : s) {
        std::cout << *v << "\n";
    }
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

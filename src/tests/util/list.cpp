/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "list.h"
#include "test.h"
using namespace lean;

static void tst1() {
    list<int> l;
    lean_assert(is_nil(l));
    for (int i = 0; i < 10; i++) {
        list<int> old = l;
        l = list<int>(i, l);
        lean_assert(!is_nil(l));
        lean_assert(car(l) == i);
        lean_assert(cdr(l) == old);
    }
    std::cout << l << "\n";
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <locale>
#include "environment.h"
#include "test.h"
using namespace lean;

static void tst1() {
    environment env;
    level l1 = env.define_uvar("l1", level());
    level l2 = env.define_uvar("l2", l1 + 10);
    level l3 = env.define_uvar("l3", max(l2, l1 + 3));
    level l4 = env.define_uvar("l4", max(l1 + 8, max(l2 + 2, l3 + 20)));
    env.display_uvars(std::cout);
    lean_assert(env.is_implied(l4 + 10, l3 + 30));
    lean_assert(!env.is_implied(l4 + 9, l3 + 30));
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

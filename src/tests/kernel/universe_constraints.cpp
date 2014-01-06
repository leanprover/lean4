/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/universe_constraints.h"
using namespace lean;

static void tst1() {
    universe_constraints uc;
    name a("a"), b("b"), c("c"), d("d");
    uc.add_var(a); uc.add_var(b); uc.add_var(c); uc.add_var(d);
    lean_assert(*(uc.get_distance(a, a)) == 0);
    lean_assert(!uc.get_distance(a, b));
    uc.add_constraint(a, b, 1);
    lean_assert(uc.is_consistent(a, b, 1));
    lean_assert(*(uc.get_distance(a, b)) == 1);
    uc.add_constraint(a, c, 1);
    lean_assert(uc.is_consistent(b, c, 1));
    lean_assert(*(uc.get_distance(a, c)) == 1);
    lean_assert(uc.is_implied(a, c, 1));
    lean_assert(!uc.is_implied(a, c, 2));
    lean_assert(uc.is_implied(a, c, 0));
    lean_assert(!uc.is_implied(b, c, 0));
    lean_assert(!uc.is_implied(a, d, 3));
    lean_assert(uc.is_consistent(a, d, 2));
    lean_assert(uc.is_consistent(c, d, 1));
    uc.add_constraint(c, d, 1);
    lean_assert(*(uc.get_distance(a, d)) == 2);
    lean_assert(uc.is_implied(a, d, 2));
    lean_assert(!uc.is_implied(a, d, 3));
    uc.add_constraint(b, d, 2);
    lean_assert(*(uc.get_distance(a, d)) == 3);
    lean_assert(uc.is_implied(a, d, 3));
    lean_assert(!uc.is_consistent(d, a, 0));
    lean_assert(!uc.is_consistent(d, a, -2));
    lean_assert(uc.is_consistent(d, a, -3));
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}


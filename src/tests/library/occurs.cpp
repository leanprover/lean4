/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/abstract.h"
#include "library/occurs.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr T = Type;
    expr a1 = Local("a", T);
    lean_assert(occurs(f, f));
    lean_assert(!occurs(a, f));
    lean_assert(occurs(a, f(a)));
    lean_assert(occurs("a", f(a)));
    lean_assert(!occurs("b", f));
    lean_assert(!occurs(a, Fun(a1, f(a1))));
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}

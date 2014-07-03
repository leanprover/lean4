/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "library/unifier.h"
using namespace lean;

static void tst1() {
    environment env;
    name_generator ngen("foo");
    expr A  = Local("A", Type);
    expr f  = Local("f", A >> (A >> A));
    expr a  = Local("a", A);
    expr b  = Local("b", A);
    expr m  = mk_metavar("m", A);
    expr t1 = f(m, m);
    expr t2 = f(a, b);
    auto r = unify(env, t1, t2, ngen);
    lean_assert(r.is_nil());
}

int main() {
    save_stack_info();
    tst1();
    return has_violations() ? 1 : 0;
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "occurs.h"
#include "abstract.h"
using namespace lean;

static void tst1() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    expr T = Type();
    lean_assert(occurs(f, f));
    lean_assert(!occurs(a, f));
    lean_assert(occurs(a, f(a)));
    lean_assert(occurs("a", f(a)));
    lean_assert(!occurs("b", f));
    lean_assert(!occurs(a, Fun({a, T}, f(a))));
    context c;
    c = extend(c, name("x"), T);
    lean_assert(!occurs(f, c));
    lean_assert(occurs(f, c, {a, f(a)}));
    lean_assert(occurs(f(a), c, {a, f(a)}));
    lean_assert(!occurs(f(b), c, {a, f(a)}));
    lean_assert(occurs("f", c, {a, f(a)}));
    lean_assert(!occurs(b, c, {a, f(a)}));
    c = extend(c, name("y"), T, f(a));
    lean_assert(!occurs("x", c));
    lean_assert(occurs(f, c));
    lean_assert(occurs("f", c));
    c = extend(c, name("z"), T, f(Const("x")));
    lean_assert(occurs("x", c));
    lean_assert(occurs("a", c));
    lean_assert(occurs(f(Const("x")), c));
    lean_assert(!occurs(f(b), c));
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

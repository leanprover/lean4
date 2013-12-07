/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "kernel/occurs.h"
#include "kernel/abstract.h"
#include "kernel/printer.h"
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

static void tst2() {
    expr f = Const("f");
    expr a = Const("a");
    expr b = Const("b");
    context c;
    c = extend(c, "a", Type());
    std::cout << c;
    lean_assert(c.size() == 1);
    lean_assert(lookup(c, 0).get_name() == "a");
    auto p = lookup_ext(c, 0);
    lean_assert(p.first.get_name() == "a");
    lean_assert(p.second.size() == 0);
}

int main() {
    save_stack_info();
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

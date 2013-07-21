/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "name.h"
#include "test.h"
using namespace lean;

static void tst1() {
    name n("foo");
    lean_assert(n == name("foo"));
    lean_assert(n != name(1));
    lean_assert(name(n, 1) != name(n, 2));
    lean_assert(name(n, 1) == name(n, 1));
    lean_assert(name(name(n, 1), 2) != name(name(n, 1), 1));
    lean_assert(name(name(n, 1), 1) == name(name(n, 1), 1));
    lean_assert(name(name(n, 2), 1) != name(name(n, 1), 1));
    lean_assert(name(name(n, "bla"), 1) == name(name(n, "bla"), 1));
    lean_assert(name(name(n, "foo"), 1) != name(name(n, "bla"), 1));
    lean_assert(name(name(name("f"), "bla"), 1) != name(name(n, "bla"), 1));
    lean_assert(n != name());
    lean_assert(name().get_kind() == name::kind::ANONYMOUS);
    lean_assert(name(name(), "foo") == name("foo"));
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

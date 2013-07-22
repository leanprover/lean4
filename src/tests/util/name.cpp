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
    lean_assert(name().kind() == name_kind::ANONYMOUS);
    lean_assert(name(name(), "foo") == name("foo"));

    lean_assert(name(n, 1) < name(n, 2));
    std::cout << "cmp(" << name(n, 1) << ", " << name(n, 2) << ") = " << cmp(name(n,1), name(n, 2)) << "\n";
    lean_assert(!(name(n, 1) >= name(n, 2)));
    lean_assert(name(n, 1) < name(name(n, 1), 1));
    lean_assert(n < name(n, 1));
    lean_assert(name(n, 2) > name(name(n, 1), 1));
    lean_assert(name(name("aa"), 2) < name(name(n, 1), 1));
    lean_assert(name(n, "aaa") < name(n, "xxx"));
    lean_assert(name(n, 1) < name(n, "xxx"));
    lean_assert(name(n, 1) < name(name(n, "xxx"), 1));
    lean_assert(name() < name(name(n, "xxx"), 1));
    lean_assert(name(1) < name(name(n, "xxx"), 1));
    lean_assert(name(1) < name(2));
    lean_assert(name(2) > name(1));
    lean_assert(name(1) > name());
    lean_assert(name(2) < name(name("foo"), 1));
    lean_assert(name(0u) < name(name(1), "foo"));
    lean_assert(name(2) > name(name(1), "foo"));
}

int main() {
    continue_on_violation(true);
    tst1();
    return has_violations() ? 1 : 0;
}

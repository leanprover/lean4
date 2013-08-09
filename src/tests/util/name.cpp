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

static name mk_big_name(unsigned num) {
    name n("foo");
    for (unsigned i = 0; i < num; i++) {
        n = name(n, "bla");
    }
    return n;
}

static void tst2() {
    name n1 = mk_big_name(2000);
    name n2 = mk_big_name(2000);
    lean_assert(n1.hash() == n2.hash());
    for (unsigned i = 0; i < 10000; i++)
        n1.hash();
    std::cout << "n1.hash(): " << n1.hash() << "\n";
}

static void tst3() {
    name n{"foo", "bla", "tst"};
    std::cout << n << "\n";
    lean_assert(n == name(name(name("foo"), "bla"), "tst"));
}

int main() {
    continue_on_violation(true);
    tst1();
    tst2();
    tst3();
    return has_violations() ? 1 : 0;
}

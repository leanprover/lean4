/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstring>
#include <sstream>
#include "test.h"
#include "name.h"
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

static void tst4() {
    lean_assert(is_prefix_of(name{"foo", "bla"}, name{"foo", "bla"}));
    lean_assert(is_prefix_of(name{"foo", "bla"}, name{"foo", "bla", "foo"}));
    lean_assert(is_prefix_of(name{"foo"}, name{"foo", "bla", "foo"}));
    lean_assert(!is_prefix_of(name{"foo"}, name{"fo", "bla", "foo"}));
    lean_assert(!is_prefix_of(name{"foo", "bla", "foo"}, name{"foo", "bla"}));
    lean_assert(is_prefix_of(name{"foo", "bla"}, name(name{"foo", "bla"}, 0u)));
    lean_assert(is_prefix_of(name(name(0u), 1u), name(name(0u), 1u)));
    lean_assert(!is_prefix_of(name(name(0u), 3u), name(name(0u), 1u)));
    lean_assert(is_prefix_of(name(name(0u), 1u), name(name(name(0u), 1u), "foo")));
    lean_assert(!is_prefix_of(name(name(2u), 1u), name(name(name(0u), 1u), "foo")));
    lean_assert(!is_prefix_of(name(name(0u), 3u), name(name(name(0u), 1u), "foo")));
    lean_assert(!is_prefix_of(name(name("bla"), 1u), name(name(name(0u), 1u), "foo")));
}

static void tst5() {
    name n(0u);
    lean_assert(n.size() == 1);
    lean_assert(name().size() > 0);
    lean_assert(name({"foo", "bla", "boing"}).get_prefix() == name({"foo", "bla"}));
    lean_assert(!name({"foo", "bla", "boing"}).is_atomic());
    lean_assert(name({"foo"}).is_atomic());
    lean_assert(strcmp(name({"foo", "bla", "boing"}).get_string(), "boing") == 0);
    lean_assert(name(name(0u), 1u).get_numeral() == 1u);
    lean_assert(name(2u).get_numeral() == 2u);
    lean_assert(name::anonymous().is_anonymous());
    name n1("foo");
    name n2 = n1;
    lean_assert(n2 == n1);
    std::cout << name::anonymous() << "\n";
    std::cout << name({"foo", "bla", "boing"}).get_prefix() << "\n";
    lean_assert(name("foo").is_string());
    lean_assert(name(0u).is_numeral());
    lean_assert(name(name(0u), "foo").is_string());
    lean_assert(name(name("foo"), 0u).is_numeral());
    lean_assert(name(name(0u), "foo").get_prefix().is_numeral());
    lean_assert(name(name("foo"), 0u).get_prefix().is_string());
}

int main() {
    tst1();
    tst2();
    tst3();
    tst4();
    tst5();
    return has_violations() ? 1 : 0;
}

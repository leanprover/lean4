/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/trie.h"
using namespace lean;

static void tst1() {
    ctrie<int> t;
    lean_assert(!find(t, "hello"));
    t = insert(t, "hello", 3);
    lean_assert(*find(t, "hello") == 3);
    lean_assert(!find(t, "hell"));
    lean_assert(!find(t, "hellow"));
    t = insert(t, "hallo", 2);
    t = insert(t, "hell",  5);
    lean_assert(*find(t, "hallo") == 2);
    lean_assert(*find(t, "hell") == 5);
    lean_assert(*find(t, "hello") == 3);
    lean_assert(!find(t, "hel"));
    ctrie<int> t2 = t;
    t2 = insert(t2, "abc", 10);
    t2 = insert(t2, "abd", 11);
    t2 = insert(t2, "help", 12);
    lean_assert(*find(t2, "abd") == 11);
    lean_assert(!find(t, "abd"));
    t2.display(std::cout);
    ctrie<int> t3 = *t2.find('a');
    lean_assert(!t3.value());
    lean_assert(*find(t3, "bc") == 10);
    lean_assert(*find(t3, "bd") == 11);
    ctrie<int> t4 = *(t3.find('b')->find('c'));
    lean_assert(*t4.value() == 10);
}

static void tst2() {
    ctrie<int> t1;
    t1 = insert(t1, "hello", 1);
    t1 = insert(t1, "abc", 2);
    t1 = insert(t1, "hallo", 3);

    ctrie<int> t2;
    t2 = insert(t2, "hell", 11);
    t2 = insert(t2, "abd", 12);
    t2 = insert(t2, "heaaaaaa", 13);
    t2 = insert(t2, "hallo", 14);
    t2 = insert(t2, "abe", 15);

    t1.merge(t2);

    lean_assert(*find(t1, "hallo") == 14);
    lean_assert(*find(t1, "hello") == 1);
    lean_assert(*find(t1, "heaaaaaa") == 13);
    lean_assert(*find(t1, "abc") == 2);
    lean_assert(*find(t1, "abd") == 12);
    lean_assert(!find(t2, "abc"));
    lean_assert(*find(t2, "abd") == 12);
    std::cout << "---------\n";
    t1.display(std::cout);
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

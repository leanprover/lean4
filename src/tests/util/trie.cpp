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
    ctrie<int> t3 = *t2.find('a');
    lean_assert(*find(t3, "bc") == 10);
    lean_assert(*find(t3, "bd") == 11);
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

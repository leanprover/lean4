/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/scoped_set.h"
using namespace lean;

static void tst1() {
    scoped_set<int> s;
    lean_assert(s.empty());
    lean_assert(s.size() == 0);
    lean_assert(s.find(10) == s.end());
    s.insert(10);
    lean_assert(!s.empty());
    lean_assert(s.size() == 1);
    lean_assert(s.find(10) != s.end());
    lean_assert(s.num_scopes() == 0);
    lean_assert(s.at_base_lvl());
    s.push();
    lean_assert(s.num_scopes() == 1);
    lean_assert(!s.at_base_lvl());
    s.insert(20);
    lean_assert(s.find(20) != s.end());
    lean_assert(s.find(30) == s.end());
    s.insert(10);
    lean_assert(s.size() == 2);
    s.pop();
    lean_assert(s.size() == 1);
    lean_assert(s.find(10) != s.end());
    lean_assert(s.find(20) == s.end());
    s.push();
    s.insert(30);
    lean_assert(s.size() == 2);
    s.erase(10);
    lean_assert(s.size() == 1);
    s.push();
    lean_assert(s.num_scopes() == 2);
    lean_assert(!s.at_base_lvl());
    s.erase(10);
    lean_assert(s.size() == 1);
    s.pop();
    lean_assert(s.num_scopes() == 1);
    lean_assert(s.find(10) == s.end());
    lean_assert(s.find(30) != s.end());
    lean_assert(s.size() == 1);
    s.pop();
    lean_assert(s.size() == 1);
    lean_assert(s.at_base_lvl());
    lean_assert(s.find(10) != s.end());
    lean_assert(s.find(30) == s.end());
}

int main() {
    tst1();
    return has_violations() ? 1 : 0;
}

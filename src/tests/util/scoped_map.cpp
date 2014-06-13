/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/scoped_map.h"
using namespace lean;

static void tst1() {
    scoped_map<int, int> s;
    lean_assert(s.empty());
    lean_assert(s.size() == 0);
    lean_assert(s.find(10) == s.end());
    s.insert(10, 20);
    lean_assert(!s.empty());
    lean_assert(s.size() == 1);
    lean_assert(s.find(10) != s.end());
    lean_assert(s.find(10)->second == 20);
    lean_assert(s.num_scopes() == 0);
    lean_assert(s.at_base_lvl());
    s.push();
    lean_assert(s.num_scopes() == 1);
    lean_assert(!s.at_base_lvl());
    s.insert(20, 40);
    lean_assert(s.find(20) != s.end());
    lean_assert(s.find(30) == s.end());
    s.insert(10, 30);
    lean_assert(s.find(10)->second == 30);
    lean_assert(s.size() == 2);
    s.pop();
    lean_assert(s.size() == 1);
    lean_assert(s.find(10) != s.end());
    lean_assert(s.find(10)->second == 20);
    lean_assert(s.find(20) == s.end());
    s.push();
    s.insert(30, 50);
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

static void tst2() {
    scoped_map<int, int> s;
    s.push();
    s.insert(10, 20);
    lean_assert(s.find(10)->second == 20);
    lean_assert(s.contains(10));
    s.pop();
    lean_assert(!s.contains(10));
    s.push();
    s.insert(10, 30);
    lean_assert(s.find(10)->second == 30);
    lean_assert(s.num_scopes() == 1);
    s.keep();
    lean_assert(s.num_scopes() == 0);
    lean_assert(s.find(10)->second == 30);
    s.push();
    s.push();
    s.insert(1, 3);
    lean_assert(s.num_scopes() == 2);
    lean_assert(s.find(1)->second == 3);
    s.keep();
    lean_assert(s.find(1)->second == 3);
    lean_assert(s.num_scopes() == 1);
    lean_assert(s.size() == 2);
    s.pop();
    lean_assert(!s.contains(1));
    lean_assert(s.num_scopes() == 0);
    lean_assert(s.find(10)->second == 30);
    lean_assert(s.size() == 1);
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

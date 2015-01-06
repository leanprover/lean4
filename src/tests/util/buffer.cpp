/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/test.h"
#include "util/buffer.h"
using namespace lean;

template<typename C>
static void loop(int n) {
    C b;
    b.push_back(n);
    lean_assert(b.size() == 1);
    lean_assert(b.back() == n);
    lean_assert(b[0] == n);
    if (n > 0)
        loop<C>(n-1);
}

static void tst1() {
    buffer<int> b1;
    buffer<int> b2;
    b1.push_back(10);
    lean_assert(b1 != b2);
    b2.push_back(20);
    lean_assert(b1 != b2);
    b2.pop_back();
    b2.push_back(10);
    lean_assert(b1 == b2);
    b2.push_back(20);
    b2.push_back(20);
    lean_assert(b1 != b2);
    b2.shrink(1);
    lean_assert(b1 == b2);
    b2.push_back(100);
    lean_assert(b1 != b2);
    b2 = b1;
    lean_assert(b1 == b2);
    buffer<int> b3(b1);
    lean_assert(b3 == b1);
    lean_assert(b1.back() == 10);
}

static void tst2() {
    buffer<int> b1;
    buffer<int> b2;
    b1.push_back(1); b1.push_back(2); b1.push_back(3);
    b2 = b1;
    lean_assert(b1.size() == 3);
    b2.resize(2);
    lean_assert(b2.size() == 2);
    b2.resize(10, 0);
    lean_assert(b2.size() == 10);
    b2.resize(1);
    lean_assert(b2.size() == 1);
}

static void check(buffer<int> const & b, std::initializer_list<int> const & l) {
    lean_assert(b.size() == l.size());
    unsigned i = 0;
    for (int v : l) {
        lean_assert(b[i] == v);
        i++;
    }
}

static void tst3() {
    buffer<int> b;
    for (unsigned i = 0; i < 5; i++)
        b.push_back(i);
    b.insert(0, 1000);
    check(b, {1000, 0, 1, 2, 3, 4});
    b.insert(1, 2000);
    check(b, {1000, 2000, 0, 1, 2, 3, 4});
    b.insert(6, 100);
    check(b, {1000, 2000, 0, 1, 2, 3, 100, 4});
    b.insert(8, 300);
    check(b, {1000, 2000, 0, 1, 2, 3, 100, 4, 300});
}

static void tst4() {
    buffer<buffer<int>> b;
    for (unsigned j = 38; j < 40; j++) {
        for (unsigned i = 0; i < j; i++) {
            b.push_back(buffer<int>());
            for (unsigned k = 0; k < 10; k++) {
                b.back().push_back(k);
            }
        }
        lean_assert(b.size() == j);
        b.clear();
        lean_assert(b.size() == 0);
    }
}

int main() {
    loop<buffer<int>>(100);
    tst1();
    tst2();
    tst3();
    tst4();
    return has_violations() ? 1 : 0;
}

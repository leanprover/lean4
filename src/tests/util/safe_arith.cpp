/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <limits>
#include "util/test.h"
#include "util/safe_arith.h"
using namespace lean;

template<typename K>
void add(int v, K k) {
    try {
        safe_add(v, k);
    } catch (exception & ex) {
        lean_assert(false, v, k);
    }
}

template<typename K>
void add_overflow(int v, K k) {
    try {
        int r = safe_add(v, k);
        lean_assert(false, v, k, r);
    } catch (exception & ex) {
        std::cout << "expected under/overflow: " << v << ", " << k << ", " << ex.what() << "\n";
    }
}

template<typename K>
void sub(int v, K k) {
    try {
        safe_sub(v, k);
    } catch (exception & ex) {
        lean_assert(false, v, k);
    }
}

template<typename K>
void sub_overflow(int v, K k) {
    try {
        int r = safe_sub(v, k);
        lean_assert(false, v, k, r);
    } catch (exception & ex) {
        std::cout << "expected under/overflow: " << v << ", " << k << ", " << ex.what() << "\n";
    }
}

static void tst1() {
    add_overflow(1 << 30, 1u << 31);
    add_overflow(1 << 30, 1 << 30);
    add_overflow(std::numeric_limits<int>::max(), 1);
    add_overflow(std::numeric_limits<int>::max(), 1u);
    add_overflow(std::numeric_limits<int>::max(), 2);
    add_overflow(std::numeric_limits<int>::max(), 2u);
    add_overflow(std::numeric_limits<int>::max()/2 + 1, std::numeric_limits<int>::max()/2 + 1);
    add(1 << 30, (1 << 30) - 1);
    add(1 << 30, 1);
    add(1 << 30, (1u << 30) - 1u);
    add(1 << 30, 1u);
    add(std::numeric_limits<int>::max(), 0);
    add(std::numeric_limits<int>::max() - 1, 1);
}

static void tst2() {
    sub_overflow(-(1 << 30), 1u << 31);
    sub_overflow(-(1 << 30), (1 << 30) + 1);
    sub_overflow(std::numeric_limits<int>::min(), 1);
    sub_overflow(std::numeric_limits<int>::min(), 1u);
    sub_overflow(std::numeric_limits<int>::min(), 2);
    sub_overflow(std::numeric_limits<int>::min(), 2u);
    sub_overflow(std::numeric_limits<int>::min()/2 - 1, std::numeric_limits<int>::max()/2 + 1);
    sub(-(1 << 30), (1 << 30) - 1);
    sub(-(1 << 30), 1);
    sub(-(1 << 30), (1u << 30));
    sub(-(1 << 30), 1u);
    sub(std::numeric_limits<int>::min(), 0);
    sub(std::numeric_limits<int>::min() + 1, 1);
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

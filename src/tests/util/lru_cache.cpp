/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/test.h"
#include "util/lru_cache.h"
using namespace lean;

static void tst1(int C = 10000) {
    lru_cache<int> m_cache(C);
    for (int i = 0; i < 2*C; i++) {
        lean_verify(m_cache.insert(i) == nullptr);
    }
    for (int i = C; i < 2*C; i++) {
        lean_verify(*m_cache.insert(i) == i);
    }
    lean_assert(m_cache.size() == static_cast<unsigned>(C));
    for (int i = 0; i < C; i++) {
        lean_assert(!m_cache.contains(i));
    }
    for (int i = C; i < 2*C; i++) {
        lean_assert(m_cache.contains(i));
    }
    m_cache.set_capacity(C/2);
    lean_assert(m_cache.capacity() == static_cast<unsigned>(C/2));
    for (int i = C; i < C + C/2; i++) {
        lean_assert(!m_cache.contains(i));
    }
    for (int i = C + C/2; i < 2*C; i++) {
        lean_assert(m_cache.contains(i));
    }
    for (int i = C + C/2; i < 2*C; i++) {
        lean_assert(*m_cache.find(i) == i);
        m_cache.erase(i);
        lean_assert(!m_cache.contains(i));
    }
    lean_assert(m_cache.size() == 0);
}

static void tst2() {
    lru_cache<int> m_cache(5);
    for (int i = 0; i < 10; i++) {
        m_cache.insert(i);
    }
    lean_assert(m_cache.size() == 5);
    m_cache.clear();
    lean_assert(m_cache.empty());
}

int main() {
    tst1();
    tst2();
    return has_violations() ? 1 : 0;
}

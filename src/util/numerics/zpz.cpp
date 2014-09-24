/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/debug.h"
#include "util/numerics/gcd.h"
#include "util/numerics/zpz.h"

namespace lean {
void zpz::inv() {
    lean_assert(m_value != 0);
    lean_assert(is_normalized());
    // eulers theorem a^(p - 2), but gcd could be more efficient
    // a*t1 + p*t2 = 1 => a*t1 = 1 (mod p) => t1 is the inverse (t3 == 1)
    int64 g, a, b;
    gcdext(g, a, b, static_cast<int64>(m_value), static_cast<int64>(m_p));
    m_value = remainder(a, static_cast<int64>(m_p));
}

static zpz * g_zero = nullptr;
zpz const & numeric_traits<zpz>::zero() {
    return *g_zero;
}
void initialize_zpz() {
    g_zero = new zpz();
}
void finalize_zpz() {
    delete g_zero;
}
}

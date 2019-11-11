/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_cache.h"

namespace lean {
expr * expr_cache::find(expr const & e) {
    unsigned i = hash(e) % m_capacity;
    if (m_cache[i].m_expr && is_bi_equal(*m_cache[i].m_expr, e))
        return &m_cache[i].m_result;
    else
        return nullptr;
}

void expr_cache::insert(expr const & e, expr const & v) {
    unsigned i = hash(e) % m_capacity;
    if (!m_cache[i].m_expr)
        m_used.push_back(i);
    m_cache[i].m_expr   = e;
    m_cache[i].m_result = v;
}

void expr_cache::clear() {
    for (unsigned i : m_used) {
        m_cache[i].m_expr   = none_expr();
        m_cache[i].m_result = expr();
    }
    m_used.clear();
}
}

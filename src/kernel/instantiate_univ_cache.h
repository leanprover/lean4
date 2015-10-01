/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <limits>
#include <vector>
#include "kernel/declaration.h"

namespace lean {
class instantiate_univ_cache {
    typedef std::tuple<declaration, levels, expr> entry;
    unsigned                     m_capacity;
    std::vector<optional<entry>> m_cache;
public:
    instantiate_univ_cache(unsigned capacity):m_capacity(capacity) {
        if (m_capacity == 0)
            m_capacity++;
    }

    optional<expr> is_cached(declaration const & d, levels const & ls) {
        if (m_cache.empty())
            return none_expr();
        lean_assert(m_cache.size() == m_capacity);
        unsigned idx = d.get_name().hash() % m_capacity;
        if (auto it = m_cache[idx]) {
            declaration d_c; levels ls_c; expr r_c;
            std::tie(d_c, ls_c, r_c) = *it;
            if (!is_eqp(d_c, d))
                return none_expr();
            if (ls == ls_c)
                return some_expr(r_c);
            else
                return none_expr();
        }
        return none_expr();
    }

    void save(declaration const & d, levels const & ls, expr const & r) {
        if (m_cache.empty())
            m_cache.resize(m_capacity);
        lean_assert(m_cache.size() == m_capacity);
        unsigned idx = d.get_name().hash() % m_cache.size();
        m_cache[idx] = entry(d, ls, r);
    }

    void clear() {
        m_cache.clear();
        lean_assert(m_cache.empty());
    }
};
}

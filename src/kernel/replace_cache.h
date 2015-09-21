/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "kernel/expr.h"

namespace lean {
struct replace_cache {
    struct entry {
        expr_cell * m_cell;
        unsigned    m_offset;
        expr        m_result;
        entry():m_cell(nullptr) {}
    };
    unsigned              m_capacity;
    std::vector<entry>    m_cache;
    std::vector<unsigned> m_used;
    replace_cache(unsigned c):m_capacity(c), m_cache(c) {}

    expr * find(expr const & e, unsigned offset) {
        unsigned i = hash(e.hash_alloc(), offset) % m_capacity;
        if (m_cache[i].m_cell == e.raw() && m_cache[i].m_offset == offset)
            return &m_cache[i].m_result;
        else
            return nullptr;
    }

    void insert(expr const & e, unsigned offset, expr const & v) {
        unsigned i = hash(e.hash_alloc(), offset) % m_capacity;
        if (m_cache[i].m_cell == nullptr)
            m_used.push_back(i);
        m_cache[i].m_cell   = e.raw();
        m_cache[i].m_offset = offset;
        m_cache[i].m_result = v;
    }

    void clear() {
        for (unsigned i : m_used) {
            m_cache[i].m_cell   = nullptr;
            m_cache[i].m_result = expr();
        }
        m_used.clear();
    }
};
}

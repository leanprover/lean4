/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include "kernel/expr.h"

namespace lean {
/** \brief Cache for storing mappings from expressions to expressions.

    \warning The insert(k, v) method overwrites andy entry (k1, v1) when
    hash(k) == hash(k1)
*/
class expr_cache {
    struct entry {
        optional<expr> m_expr;
        expr           m_result;
    };
    unsigned              m_capacity;
    std::vector<entry>    m_cache;
    std::vector<unsigned> m_used;
public:
    expr_cache(unsigned c):m_capacity(c), m_cache(c) {}
    void insert(expr const & e, expr const & v);
    expr * find(expr const & e);
    void clear();
};
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/hash.h"
#include "kernel/expr.h"
#include "library/expr_lt.h"

namespace lean {
typedef pair<expr, expr> expr_pair;
/** \brief Functional object for hashing expression pairs. */
struct expr_pair_hash {
    unsigned operator()(expr_pair const & p) const { return hash(p.first.hash(), p.second.hash()); }
};
/** \brief Functional object for hashing expression pairs (based on their allocation time). */
struct expr_pair_hash_alloc {
    unsigned operator()(expr_pair const & p) const { return hash(p.first.hash_alloc(), p.second.hash_alloc()); }
};
/** \brief Functional object for comparing expression pairs. */
struct expr_pair_eq {
    bool operator()(expr_pair const & p1, expr_pair const & p2) const { return p1.first == p2.first && p1.second == p2.second; }
};
/** \brief Functional object for comparing expression pairs using pointer equality. */
struct expr_pair_eqp {
    bool operator()(expr_pair const & p1, expr_pair const & p2) const { return is_eqp(p1.first, p2.first) && is_eqp(p1.second, p2.second); }
};
inline bool is_lt(expr_pair const & p1, expr_pair const & p2, bool use_hash) {
    return is_lt(p1.first, p2.first, use_hash) || (p1.first == p2.first && is_lt(p1.second, p2.second, use_hash));
}
struct expr_pair_quick_cmp {
    int operator()(expr_pair const & p1, expr_pair const & p2) const { return is_lt(p1, p2, true) ? -1 : (p1 == p2 ? 0 : 1);  }
};
}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
typedef pair<level, level> level_pair;
typedef pair<expr, expr> expr_pair;
/** \brief Functional object for hashing expression pairs. */
struct expr_pair_hash {
    unsigned operator()(expr_pair const & p) const { return hash(p.first.hash(), p.second.hash()); }
};

/** \brief Functional object for comparing expression pairs. */
struct expr_pair_eq {
    bool operator()(expr_pair const & p1, expr_pair const & p2) const { return p1.first == p2.first && p1.second == p2.second; }
};
}

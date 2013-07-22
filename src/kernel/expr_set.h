/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include "expr.h"
#include "hash.h"

namespace lean {

// =======================================
// Expression Set
// Remark: to expressions are assumed to be equal if they are "pointer-equal"
struct expr_hash {
    unsigned operator()(expr const & e) const { return e.hash(); }
};
struct expr_eqp {
    bool operator()(expr const & e1, expr const & e2) const { return eqp(e1, e2); }
};
typedef std::unordered_set<expr, expr_hash, expr_eqp> expr_set;
// =======================================

// =======================================
// (low level) Expression Cell Set
// Remark: to expressions are assumed to be equal if they are "pointer-equal"
//
// WARNING: use with care, this kind of set
// does not prevent an expression from being
// garbage collected.
struct expr_cell_hash {
    unsigned operator()(expr_cell * e) const { return e->hash(); }
};
struct expr_cell_eqp {
    bool operator()(expr_cell * e1, expr_cell * e2) const { return e1 == e2; }
};
typedef std::unordered_set<expr_cell*, expr_cell_hash, expr_cell_eqp> expr_cell_set;
// =======================================

// =======================================
// (low level) Expression Cell pair Set
// Remark: to expressions are assumed to be equal if they are "pointer-equal"
//
// WARNING: use with care, this kind of set
// does not prevent an expression from being
// garbage collected.
typedef std::pair<expr_cell *, expr_cell *> expr_cell_pair;
struct expr_cell_pair_hash {
    unsigned operator()(expr_cell_pair const & p) const { return hash(p.first->hash(), p.second->hash()); }
};
struct expr_cell_pair_eqp {
    bool operator()(expr_cell_pair const & p1, expr_cell_pair const & p2) const {
        return p1.first == p2.first && p1.second == p2.second;
    }
};
typedef std::unordered_set<expr_cell_pair, expr_cell_pair_hash, expr_cell_pair_eqp> expr_cell_pair_set;
// =======================================
}

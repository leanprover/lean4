/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include <utility>
#include <functional>
#include "util/hash.h"
#include "kernel/expr.h"

namespace lean {

// =======================================
// Expression Set && Expression Offset Set
// Remark: to expressions are assumed to be equal if they are "pointer-equal"
typedef std::unordered_set<expr, expr_hash_alloc, expr_eqp> expr_set;
typedef std::unordered_set<expr_offset, expr_offset_hash, expr_offset_eqp> expr_offset_set;
// =======================================

// =======================================
// (low level) Expression Cell Set
// Remark: to expressions are assumed to be equal if they are "pointer-equal"
//
// WARNING: use with care, this kind of set
// does not prevent an expression from being
// garbage collected.
typedef std::unordered_set<expr_cell*, expr_cell_hash, expr_cell_eqp> expr_cell_set;
typedef std::unordered_set<expr_cell_offset, expr_cell_offset_hash, expr_cell_offset_eqp> expr_cell_offset_set;
// =======================================

// =======================================
// (low level) Expression Cell pair Set
// Remark: to expressions are assumed to be equal if they are "pointer-equal"
//
// WARNING: use with care, this kind of set
// does not prevent an expression from being
// garbage collected.
typedef pair<expr_cell *, expr_cell *> expr_cell_pair;
struct expr_cell_pair_hash {
    unsigned operator()(expr_cell_pair const & p) const { return hash(p.first->hash_alloc(), p.second->hash_alloc()); }
};
struct expr_cell_pair_eqp {
    bool operator()(expr_cell_pair const & p1, expr_cell_pair const & p2) const {
        return p1.first == p2.first && p1.second == p2.second;
    }
};
typedef std::unordered_set<expr_cell_pair, expr_cell_pair_hash, expr_cell_pair_eqp> expr_cell_pair_set;
// =======================================

// Similar to expr_set, but using structural equality
typedef std::unordered_set<expr, expr_hash, std::equal_to<expr>> expr_struct_set;
}

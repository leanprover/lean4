/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr_pair.h"
#include "library/blast/branch.h"

namespace lean {
namespace blast {

namespace simp {

/* Struct to store results of simplification */
struct result {
    /* Invariant [m_pf : m_orig <rel> m_new] */
    expr m_new;
    optional<expr> m_proof;

public:
    result(expr const & e): m_new(e) {}
    result(expr const & e, expr const & pf): m_new(e), m_proof(pf) {}
    result(expr const & e, optional<expr> const & pf): m_new(e), m_proof(pf) {}

    bool is_none() const { return !static_cast<bool>(m_proof); }
    expr get_new() const { return m_new; }
    expr get_proof() const { lean_assert(m_proof); return *m_proof; }

    /* The following assumes that [e] and [m_new] are definitionally equal */
    void update(expr const & e) { m_new = e; }
};

}

simp::result simplify(branch const & b, name const & rel, expr const & e);

void initialize_simplifier();
void finalize_simplifier();

}
}

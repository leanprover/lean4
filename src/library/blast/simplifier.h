/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "kernel/expr_pair.h"
#include "library/blast/state.h"
#include "library/simplifier/simp_rule_set.h"

namespace lean {
namespace blast {

namespace simp {

/* Struct to store results of simplification */
struct result {
    /* Invariant [m_pf : m_orig <rel> m_new] */
    /* Note: we only keep [m_old] to make the code easier to understand.
       It could be optimized away in the future. */
    expr m_new;

    /* If proof is not provided, it is assumed to be reflexivity */
    optional<expr> m_proof;

public:
    result() {}
    result(expr const & e): m_new(e) {}
    result(expr const & e, expr const & proof): m_new(e), m_proof(proof) {}
    result(expr const & e, optional<expr> const & proof): m_new(e), m_proof(proof) {}

    bool has_proof() const { return static_cast<bool>(m_proof); }

    expr get_new() const { return m_new; }
    expr get_proof() const { lean_assert(m_proof); return *m_proof; }

    /* The following assumes that [e] and [m_new] are definitionally equal */
    void update(expr const & e) { m_new = e; }
};
}

simp::result simplify(name const & rel, expr const & e, simp_rule_sets const & srss);

void initialize_simplifier();
void finalize_simplifier();

}
}

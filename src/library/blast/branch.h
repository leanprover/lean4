/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "library/blast/expr.h"
#include "library/blast/hypothesis.h"

namespace lean {
namespace blast {
typedef rb_tree<unsigned, unsigned_cmp> metavar_set;

class branch {
    typedef rb_map<unsigned, hypothesis, unsigned_cmp>         context;
    typedef rb_map<unsigned, hypothesis_idx_set, unsigned_cmp> forward_deps;
    friend class state;
    unsigned           m_next;
    context            m_context;
    forward_deps       m_forward_deps; // given an entry (h -> {h_1, ..., h_n}), we have that each h_i uses h.
    expr               m_target;
    hypothesis_idx_set m_target_deps;
    metavar_set        m_mvars;

    /** \brief Mark a hypothesis as fixed. The type/value of a fixed hypothesis cannot be
        modified. A hypothesis is fixed when it occurs in the type of some metavariable. */
    void fix_hypothesis(unsigned idx);
    void fix_hypothesis(expr const & e) {
        lean_assert(is_lref(e));
        fix_hypothesis(lref_index(e));
    }

    void add_forward_dep(unsigned hidx_user, unsigned hidx_provider);
    void add_deps(expr const & e, hypothesis & h_user, unsigned hidx_user);
    void add_deps(hypothesis & h_user, unsigned hidx_user);

public:
    branch():m_next(0) {}
    /** \brief Store in \c r the hypotheses in this branch sorted by depth */
    void get_sorted_hypotheses(hypothesis_idx_buffer & r);

    expr add_hypothesis(name const & n, expr const & type, optional<expr> const & value, optional<expr> const & jst);
    expr add_hypothesis(expr const & type, optional<expr> const & value, optional<expr> const & jst);

    void set_target(expr const & t);

    hypothesis const * get(unsigned idx) const { return m_context.find(idx); }
    hypothesis const * get(expr const & e) const {
        lean_assert(is_lref(e));
        return get(lref_index(e));
    }
};

void initialize_branch();
void finalize_branch();
}}

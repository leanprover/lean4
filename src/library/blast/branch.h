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
typedef rb_tree<unsigned, unsigned_cmp> metavar_idx_set;
template<typename T>
using metavar_idx_map = typename lean::rb_map<unsigned, T, unsigned_cmp>;

class branch {
    typedef hypothesis_idx_map<hypothesis>         context;
    typedef hypothesis_idx_map<hypothesis_idx_set> forward_deps;
    friend class state;
    unsigned           m_next;
    context            m_context;
    forward_deps       m_forward_deps; // given an entry (h -> {h_1, ..., h_n}), we have that each h_i uses h.
    expr               m_target;
    hypothesis_idx_set m_target_deps;
    metavar_idx_set    m_mvar_idxs;

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

    expr add_hypothesis(name const & n, expr const & type, optional<expr> const & value, optional<expr> const & jst);
    expr add_hypothesis(expr const & type, optional<expr> const & value, optional<expr> const & jst);

    /** \brief Return true iff the hypothesis with index \c hidx_user depends on the hypothesis with index
        \c hidx_provider. */
    bool hidx_depends_on(unsigned hidx_user, unsigned hidx_provider) const;

    hypothesis const * get(unsigned hidx) const { return m_context.find(hidx); }
    hypothesis const * get(expr const & h) const {
        lean_assert(is_lref(h));
        return get(lref_index(h));
    }
    void for_each_hypothesis(std::function<void(unsigned, hypothesis const &)> const & fn) const { m_context.for_each(fn); }
    /** \brief Store in \c r the hypotheses in this branch sorted by depth */
    void get_sorted_hypotheses(hypothesis_idx_buffer & r) const;

    void set_target(expr const & t);
    expr const & get_target() const { return m_target; }
    /** \brief Return true iff the target depends on the given hypothesis */
    bool target_depends_on(expr const & h) const { return m_target_deps.contains(lref_index(h)); }

    bool has_mvar(expr const & e) const { return m_mvar_idxs.contains(mref_index(e)); }
};

void initialize_branch();
void finalize_branch();
}}

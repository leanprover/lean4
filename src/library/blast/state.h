/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_map.h"
#include "kernel/expr.h"
#include "library/blast/hypothesis.h"
#include "library/blast/branch.h"

namespace lean {
namespace blast {
class metavar_decl {
    hypothesis_idx_list m_context;
    hypothesis_idx_set  m_context_as_set;
    expr                m_type;
public:
    metavar_decl() {}
    metavar_decl(hypothesis_idx_list const & c, hypothesis_idx_set const & s, expr const & t):
        m_context(c), m_context_as_set(s), m_type(t) {}
};

class state {
    friend class context;
    unsigned m_next_mref_index;
    typedef rb_map<unsigned, metavar_decl, unsigned_cmp> metavar_decls;
    typedef rb_map<unsigned, expr, unsigned_cmp>         assignment;
    metavar_decls m_metavar_decls;
    assignment    m_assignment;
    branch        m_main;

    unsigned add_metavar_decl(metavar_decl const & decl);

public:
    state();
    /** \brief Create a new metavariable using the given type and context.
        \pre ctx must be a subset of the hypotheses in the main branch. */
    expr mk_metavar(hypothesis_idx_buffer const & ctx, expr const & type);
    /** \brief Create a new metavariable using the given type.
        The context of this metavariable will be all hypotheses occurring in the main branch. */
    expr mk_metavar(expr const & type);

    /** \brief Add a new hypothesis to the main branch */
    expr add_hypothesis(name const & n, expr const & type, optional<expr> const & value, optional<expr> const & jst) {
        return m_main.add_hypothesis(n, type, value, jst);
    }

    /** \brief Add a new hypothesis to the main branch */
    expr add_hypothesis(expr const & type, optional<expr> const & value, optional<expr> const & jst) {
        return m_main.add_hypothesis(type, value, jst);
    }

    /** \brief Set target (aka conclusion, aka type of the goal, aka type of the term that must be synthesize in this branch)
        of the main branch */
    void set_target(expr const & type) {
        return m_main.set_target(type);
    }

    metavar_decl const * get_metavar_decl(unsigned idx) const { return m_metavar_decls.find(idx); }

    metavar_decl const * get_metavar_decl(expr const & e) const { return get_metavar_decl(mref_index(e)); }
};
}}

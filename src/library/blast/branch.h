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
    typedef rb_map<unsigned, hypothesis_idx_set, unsigned_cmp> dependencies;
    friend class state;
    unsigned      m_next;
    context       m_context;
    dependencies  m_forward_deps;
    expr          m_target;
    metavar_set   m_mvars;

    /** \brief Mark a hypothesis as fixed. The type/value of a fixed hypothesis cannot be
        modified. A hypothesis is fixed when it occurs in the type of some metavariable. */
    void fix_hypothesis(unsigned idx);
    void fix_hypothesis(expr const & e) {
        lean_assert(is_lref(e));
        fix_hypothesis(lref_index(e));
    }
public:
    branch():m_next(0) {}
    /** \brief Store in \c r the hypotheses in this branch sorted by depth */
    void get_sorted_hypotheses(hypothesis_idx_buffer & r);
    hypothesis const * get(unsigned idx) const { return m_context.find(idx); }
    hypothesis const * get(expr const & e) const {
        lean_assert(is_lref(e));
        return get(lref_index(e));
    }
};
}}

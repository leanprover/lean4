/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/rb_multi_map.h"
#include "library/type_context.h"

namespace lean {
/**
   The unit propagation module can handle lemmas of the form:

       A_1 -> ... -> A_n -> B_1 \/ ... \/ B_m

   and "propagates" if one of the following conditions hold:

   - We have all A_i, and the negations of all but one B_j.
   - We have the negations of all B_j, and all but one A_i.

   Each lemma watches two of its facts. */
class unit_propagation {
public:
    class state {
        friend class unit_propagation;
        rb_multi_map<expr, expr, expr_quick_cmp> m_facts_to_lemmas;
        rb_multi_map<expr, expr, expr_quick_cmp> m_facts_to_dep_lemmas;
    public:
    };

    class assignment {
    public:
        virtual ~assignment() {}
        virtual lbool get_value(expr const & e) = 0;
        virtual optional<expr> get_proof(expr const & e) = 0;
    };

private:
    type_context & m_ctx;
    state &        m_state;
    assignment &   m_assignment;

    lbool get_value(expr const & e) { return m_assignment.get_value(e); }
    optional<expr> get_proof(expr const & e) { return m_assignment.get_proof(e); }
    void visit_lemma(expr const & e);
    void visit_dep_lemma(expr const & e);
    void propagate(expr const & e);

public:
    unit_propagation(type_context & ctx, state & s, assignment & assignment);
    void assigned(expr const & e);
};

typedef unit_propagation::state up_state;
typedef unit_propagation::assignment up_assignment;
}

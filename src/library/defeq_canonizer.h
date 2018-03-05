/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/expr_lt.h"
#include "library/type_context.h"

namespace lean {
/* \brief Return an expression that is definitionally equal to \c e.

   \remark The predicate locals_subset(r, e) holds for the resulting expression r.

   \remark updated is set to true if previous results may have been updated.

   \remark This procedure is meant to be used to canonize type class instances and
   proofs. It is too expensive for arbitrary terms.

   \remark Suppose we invoke defeq_canonize for every type class instance
   in a big term T, and we replace them with the result returned by defeq_canonize.
   If updated is not true, then forall instances I1 and I2 in the resulting term T',
   if I1 and I2 are definitionally equal and have the same local constants, then
   I1 and I2 are structurally equal.

   \remark Suppose we invoke defeq_canonize for every type class instance in a big term T,
   and updated is true in the end. Then, if we reset updated to false and restart the process,
   then eventually updated will be false after a finite number of restarts. */
class defeq_canonizer {
public:
    struct state {
        /* Canonical mapping I -> J (i.e., J is the canonical expression for I).
           Invariant: locals_subset(J, I) */
        rb_expr_map<expr>    m_C;
        /* Mapping from head symbol N to list of expressions es s.t.
           for each e in es, head_symbol(e) = N. */
        name_map<list<expr>> m_M;
    };
private:
    type_context_old & m_ctx;
    state &        m_state;
    bool *         m_updated{nullptr};

    optional<name> get_head_symbol(expr type);
    optional<expr> find_defeq(name const & h, expr const & e);
    void replace_C(expr const & e1, expr const & e2);
    void insert_C(expr const & e1, expr const & e2);
    void insert_M(name const & h, expr const & e);
    void replace_M(name const & h, expr const & e, expr const & new_e);
    expr canonize_core(expr const & e);

public:
    defeq_canonizer(type_context_old & ctx, state & s);

    expr canonize(expr const & e, bool & updated);
    expr canonize(expr const & e);

    state const & get_state() const { return m_state; }
    void set_state(state const & s) { m_state = s; }
};

inline bool is_eqp(defeq_canonizer::state const & s1, defeq_canonizer::state const & s2) {
    return is_eqp(s1.m_C, s2.m_C) && is_eqp(s1.m_M, s2.m_M);
}

void initialize_defeq_canonizer();
void finalize_defeq_canonizer();
}

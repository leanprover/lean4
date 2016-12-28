/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/tactic/ac_tactics.h"

namespace lean {
class congruence_closure;
/* Associativity and commutativity by completion */
class theory_ac {
public:
    struct occurrences {
        rb_expr_tree m_occs;
        unsigned     m_size;
    };

    struct state {
        /* Mapping from operators occurring in terms and their canonical
           representation in this module */
        rb_expr_map<expr> m_can_ops;

        /* Mapping from canonical AC operators to AC proof terms. */
        rb_expr_map<pair<expr, expr>> m_op_info;

        /* rewriting rules */
        rb_expr_map<expr_pair>   m_R;
        rb_expr_map<occurrences> m_R_lhs_occs;
        rb_expr_map<occurrences> m_R_rhs_occs;

        /* Mapping from cc terms and their normal form in the AC theory. */
        rb_expr_map<expr_pair>   m_N;
        rb_expr_map<expr>        m_N_inv;
        rb_expr_map<occurrences> m_N_rhs_occs;
    };

private:
    type_context &       m_ctx;
    congruence_closure & m_cc;
    state &              m_state;
    ac_manager           m_ac_manager;

    optional<expr> is_ac(expr const & e);

public:
    theory_ac(congruence_closure & cc, state & s);
    ~theory_ac();

    optional<expr> internalize(expr const & e, optional<expr> const & parent);
    void add_eq(expr const & e1, expr const & e2);
};

void initialize_theory_ac();
void finalize_theory_ac();
}

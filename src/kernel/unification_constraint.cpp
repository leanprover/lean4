/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/unification_constraint.h"

namespace lean {
unification_constraint_cell::unification_constraint_cell(unification_constraint_kind k, context const & c, trace const & t):
    m_kind(k), m_ctx(c), m_trace(t), m_rc(1) {
}
void unification_constraint_cell::dealloc() {
    switch (m_kind) {
    case unification_constraint_kind::Eq:
        delete static_cast<unification_constraint_eq*>(this);
        break;
    case unification_constraint_kind::Convertible:
        delete static_cast<unification_constraint_convertible*>(this);
        break;
    case unification_constraint_kind::Max:
        delete static_cast<unification_constraint_max*>(this);
        break;
    case unification_constraint_kind::Choice:
        static_cast<unification_constraint_choice*>(this)->~unification_constraint_choice();
        delete[] reinterpret_cast<char*>(this);
        break;
    }
}

unification_constraint_eq::unification_constraint_eq(context const & c, expr const & lhs, expr const & rhs, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Eq, c, t),
    m_lhs(lhs),
    m_rhs(rhs) {
}

unification_constraint_convertible::unification_constraint_convertible(context const & c, expr const & from, expr const & to, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Convertible, c, t),
    m_from(from),
    m_to(to) {
}

unification_constraint_max::unification_constraint_max(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Max, c, t),
    m_lhs1(lhs1),
    m_lhs2(lhs2),
    m_rhs(rhs) {
}

unification_constraint_choice::unification_constraint_choice(context const & c, expr const & mvar, unsigned num, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Choice, c, t),
    m_mvar(mvar),
    m_num_choices(num) {
}

unification_constraint mk_eq_constraint(context const & c, expr const & lhs, expr const & rhs, trace const & t) {
    return unification_constraint(new unification_constraint_eq(c, lhs, rhs, t));
}

unification_constraint mk_convertible_constraint(context const & c, expr const & from, expr const & to, trace const & t) {
    return unification_constraint(new unification_constraint_convertible(c, from, to, t));
}

unification_constraint mk_max_constraint(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, trace const & t) {
    return unification_constraint(new unification_constraint_max(c, lhs1, lhs2, rhs, t));
}

unification_constraint mk_choice_constraint(context const & c, expr const & mvar, unsigned num, expr const * choices, trace const & t) {
    char * mem   = new char[sizeof(unification_constraint_choice) + num*sizeof(expr)];
    unification_constraint r(new (mem) unification_constraint_choice(c, mvar, num, t));
    expr * m_choices = to_choice(r)->m_choices;
    for (unsigned i = 0; i < num; i++)
        new (m_choices+i) expr(choices[i]);
    return r;
}

unification_constraint mk_choice_constraint(context const & c, expr const & mvar, std::initializer_list<expr> const & choices, trace const & t) {
    return mk_choice_constraint(c, mvar, choices.size(), choices.begin(), t);
}
}

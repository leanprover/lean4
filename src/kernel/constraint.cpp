/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/rc.h"
#include "kernel/constraint.h"
namespace lean {
struct constraint_cell {
    void dealloc();
    MK_LEAN_RC()
    constraint_kind m_kind;
    unsigned        m_hash;
    justification   m_jst;
    constraint_cell(constraint_kind k, unsigned h, justification const & j):m_rc(1), m_kind(k), m_hash(h), m_jst(j) {}
};
struct eqc_constraint_cell : public constraint_cell {
    expr m_lhs;
    expr m_rhs;
    eqc_constraint_cell(constraint_kind k, expr const & lhs, expr const & rhs, justification const & j):
        constraint_cell(k, hash(hash(lhs.hash(), rhs.hash()), static_cast<unsigned>(k)), j),
        m_lhs(lhs), m_rhs(rhs) {}
};
struct level_constraint_cell : public constraint_cell {
    level m_lhs;
    level m_rhs;
    level_constraint_cell(level const & lhs, level const & rhs, justification const & j):
        constraint_cell(constraint_kind::Level, hash(hash(lhs), hash(rhs)), j),
        m_lhs(lhs), m_rhs(rhs) {}
};
static unsigned hash(list<expr> const & ls) {
    return is_nil(ls) ? 17 : hash(car(ls).hash(), hash(cdr(ls)));
}
struct choice_constraint_cell : public constraint_cell {
    expr       m_expr;
    list<expr> m_choices;
    choice_constraint_cell(expr const & e, list<expr> const & s, justification const & j):
        constraint_cell(constraint_kind::Choice, hash(e.hash(), hash(s)), j),
        m_expr(e), m_choices(s) {}
};

constraint::constraint(constraint_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr->get_rc() == 1); }
constraint::constraint(constraint const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
constraint::constraint(constraint && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
constraint::~constraint() { if (m_ptr) m_ptr->dec_ref(); }
constraint & constraint::operator=(constraint const & c) { LEAN_COPY_REF(c); }
constraint & constraint::operator=(constraint && c) { LEAN_MOVE_REF(c); }
constraint_kind constraint::kind() const { lean_assert(m_ptr); return m_ptr->m_kind; }
unsigned constraint::hash() const { lean_assert(m_ptr); return m_ptr->m_hash; }
justification const & constraint::get_justification() const { lean_assert(m_ptr); return m_ptr->m_jst; }

constraint mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j) {
    return constraint(new eqc_constraint_cell(constraint_kind::Eq, lhs, rhs, j));
}
constraint mk_conv_cnstr(expr const & lhs, expr const & rhs, justification const & j) {
    return constraint(new eqc_constraint_cell(constraint_kind::Convertible, lhs, rhs, j));
}
constraint mk_level_cnstr(level const & lhs, level const & rhs, justification const & j) {
    return constraint(new level_constraint_cell(lhs, rhs, j));
}
constraint mk_choice_cnstr(expr const & t, list<expr> const & s, justification const & j) {
    return constraint(new choice_constraint_cell(t, s, j));
}

bool operator==(constraint const & c1, constraint const & c2) {
    if (c1.kind() != c2.kind() || c1.hash() != c2.hash())
        return false;
    switch (c1.kind()) {
    case constraint_kind::Eq: case constraint_kind::Convertible:
        return cnstr_lhs_expr(c1) == cnstr_lhs_expr(c2) && cnstr_rhs_expr(c1) == cnstr_rhs_expr(c2);
    case constraint_kind::Level:
        return cnstr_lhs_level(c1) == cnstr_lhs_level(c2) && cnstr_rhs_level(c1) == cnstr_rhs_level(c2);
    case constraint_kind::Choice:
        return
            cnstr_choice_expr(c1) == cnstr_choice_expr(c2) &&
            compare(cnstr_choice_set(c1), cnstr_choice_set(c2), [](expr const & e1, expr const & e2) { return e1 == e2; });
    }
}

expr const & cnstr_lhs_expr(constraint const & c) { lean_assert(is_eqc_cnstr(c)); return static_cast<eqc_constraint_cell*>(c.raw())->m_lhs; }
expr const & cnstr_rhs_expr(constraint const & c) { lean_assert(is_eqc_cnstr(c)); return static_cast<eqc_constraint_cell*>(c.raw())->m_rhs; }
level const & cnstr_lhs_level(constraint const & c) {
    lean_assert(is_level_cnstr(c)); return static_cast<level_constraint_cell*>(c.raw())->m_lhs;
}
level const & cnstr_rhs_level(constraint const & c) {
    lean_assert(is_level_cnstr(c)); return static_cast<level_constraint_cell*>(c.raw())->m_rhs;
}
expr const & cnstr_choice_expr(constraint const & c) {
    lean_assert(is_choice_cnstr(c)); return static_cast<choice_constraint_cell*>(c.raw())->m_expr;
}
list<expr> const & cnstr_choice_set(constraint const & c) {
    lean_assert(is_choice_cnstr(c)); return static_cast<choice_constraint_cell*>(c.raw())->m_choices;
}

constraint updt_eqc_cnstr(constraint const & c, expr const & new_lhs, expr const & new_rhs, justification const & new_jst) {
    lean_assert(is_eqc_cnstr(c));
    if (!is_eqp(cnstr_lhs_expr(c), new_lhs) || !is_eqp(cnstr_rhs_expr(c), new_rhs)) {
        if (is_eq_cnstr(c))
            return mk_eq_cnstr(new_lhs, new_rhs, new_jst);
        else
            return mk_conv_cnstr(new_lhs, new_rhs, new_jst);
    } else {
        return c;
    }
}
constraint updt_eqc_cnstr(constraint const & c, expr const & new_lhs, expr const & new_rhs) {
    return updt_eqc_cnstr(c, new_lhs, new_rhs, c.get_justification());
}
constraint updt_level_cnstr(constraint const & c, level const & new_lhs, level const & new_rhs, justification const & new_jst) {
    lean_assert(is_level_cnstr(c));
    if (!is_eqp(cnstr_lhs_level(c), new_lhs) || !is_eqp(cnstr_rhs_level(c), new_rhs))
        return mk_level_cnstr(new_lhs, new_rhs, new_jst);
    else
        return c;
}
constraint updt_level_cnstr(constraint const & c, level const & new_lhs, level const & new_rhs) {
    return updt_level_cnstr(c, new_lhs, new_rhs, c.get_justification());
}

std::ostream & operator<<(std::ostream & out, constraint const & c) {
    switch (c.kind()) {
    case constraint_kind::Eq:
        out << cnstr_lhs_expr(c) << " ≈ " << cnstr_rhs_expr(c);
    case constraint_kind::Convertible:
        out << cnstr_lhs_expr(c) << " ↠ " << cnstr_rhs_expr(c);
    case constraint_kind::Level:
        out << cnstr_lhs_level(c) << " ≤ " << cnstr_rhs_level(c);
    case constraint_kind::Choice:
        out << cnstr_choice_expr(c) << " ∊ {";
        bool first = true;
        for (expr const & e : cnstr_choice_set(c)) {
            if (first) first = false; else out << ", ";
            out << e;
        }
        out << "}";
    }
    return out;
}
}

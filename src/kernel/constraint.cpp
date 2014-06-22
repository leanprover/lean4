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
    justification   m_jst;
    constraint_cell(constraint_kind k, justification const & j):m_rc(1), m_kind(k), m_jst(j) {}
};
struct eq_constraint_cell : public constraint_cell {
    expr m_lhs;
    expr m_rhs;
    eq_constraint_cell(expr const & lhs, expr const & rhs, justification const & j):
        constraint_cell(constraint_kind::Eq, j),
        m_lhs(lhs), m_rhs(rhs) {}
};
struct level_constraint_cell : public constraint_cell {
    level m_lhs;
    level m_rhs;
    level_constraint_cell(level const & lhs, level const & rhs, justification const & j):
        constraint_cell(constraint_kind::LevelEq, j),
        m_lhs(lhs), m_rhs(rhs) {}
};
struct choice_constraint_cell : public constraint_cell {
    expr      m_mvar;
    choice_fn m_fn;
    choice_constraint_cell(expr const & mvar, choice_fn const & fn, justification const & j):
        constraint_cell(constraint_kind::Choice, j),
        m_mvar(mvar), m_fn(fn) {}
};

void constraint_cell::dealloc() {
    switch (m_kind) {
    case constraint_kind::Eq:
        delete static_cast<eq_constraint_cell*>(this); break;
    case constraint_kind::LevelEq:
        delete static_cast<level_constraint_cell*>(this); break;
    case constraint_kind::Choice:
        delete static_cast<choice_constraint_cell*>(this); break;
    }
}

constraint::constraint(constraint_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr->get_rc() == 1); }
constraint::constraint(constraint const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
constraint::constraint(constraint && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
constraint::~constraint() { if (m_ptr) m_ptr->dec_ref(); }
constraint & constraint::operator=(constraint const & c) { LEAN_COPY_REF(c); }
constraint & constraint::operator=(constraint && c) { LEAN_MOVE_REF(c); }
constraint_kind constraint::kind() const { lean_assert(m_ptr); return m_ptr->m_kind; }
justification const & constraint::get_justification() const { lean_assert(m_ptr); return m_ptr->m_jst; }

constraint mk_eq_cnstr(expr const & lhs, expr const & rhs, justification const & j) {
    return constraint(new eq_constraint_cell(lhs, rhs, j));
}
constraint mk_level_eq_cnstr(level const & lhs, level const & rhs, justification const & j) {
    return constraint(new level_constraint_cell(lhs, rhs, j));
}
constraint mk_choice_cnstr(expr const & m, choice_fn const & fn, justification const & j) {
    lean_assert(is_meta(m));
    return constraint(new choice_constraint_cell(m, fn, j));
}

expr const & cnstr_lhs_expr(constraint const & c) { lean_assert(is_eq_cnstr(c)); return static_cast<eq_constraint_cell*>(c.raw())->m_lhs; }
expr const & cnstr_rhs_expr(constraint const & c) { lean_assert(is_eq_cnstr(c)); return static_cast<eq_constraint_cell*>(c.raw())->m_rhs; }
level const & cnstr_lhs_level(constraint const & c) {
    lean_assert(is_level_eq_cnstr(c));
    return static_cast<level_constraint_cell*>(c.raw())->m_lhs;
}
level const & cnstr_rhs_level(constraint const & c) {
    lean_assert(is_level_eq_cnstr(c));
    return static_cast<level_constraint_cell*>(c.raw())->m_rhs;
}
expr const & cnstr_mvar(constraint const & c) { lean_assert(is_choice_cnstr(c)); return static_cast<choice_constraint_cell*>(c.raw())->m_mvar; }
choice_fn const & cnstr_choice_fn(constraint const & c) {
    lean_assert(is_choice_cnstr(c)); return static_cast<choice_constraint_cell*>(c.raw())->m_fn;
}

constraint update_justification(constraint const & c, justification const & j) {
    switch (c.kind()) {
    case constraint_kind::Eq:
        return mk_eq_cnstr(cnstr_lhs_expr(c), cnstr_rhs_expr(c), j);
    case constraint_kind::LevelEq:
        return mk_level_eq_cnstr(cnstr_lhs_level(c), cnstr_rhs_level(c), j);
    case constraint_kind::Choice:
        return mk_choice_cnstr(cnstr_mvar(c), cnstr_choice_fn(c), j);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

std::ostream & operator<<(std::ostream & out, constraint const & c) {
    switch (c.kind()) {
    case constraint_kind::Eq:
        out << cnstr_lhs_expr(c) << " ≈ " << cnstr_rhs_expr(c);
        break;
    case constraint_kind::LevelEq:
        out << cnstr_lhs_level(c) << " = " << cnstr_rhs_level(c);
        break;
    case constraint_kind::Choice:
        out << "choice " << cnstr_mvar(c);
        break;
    }
    return out;
}
}

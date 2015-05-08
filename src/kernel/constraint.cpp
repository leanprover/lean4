/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/rc.h"
#include "kernel/expr.h"
#include "kernel/justification.h"
#include "kernel/metavar.h"
#include "kernel/constraint.h"

namespace lean {
struct constraint_cell {
    void dealloc();
    MK_LEAN_RC()
    constraint_kind m_kind;
    justification   m_jst;
    constraint_cell(constraint_kind k, justification const & j):
        m_rc(1), m_kind(k), m_jst(j) {}
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
    expr         m_expr;
    choice_fn    m_fn;
    delay_factor m_delay_factor;
    bool         m_owner;
    choice_constraint_cell(expr const & e, choice_fn const & fn, delay_factor const & f,
                           bool owner, justification const & j):
        constraint_cell(constraint_kind::Choice, j),
        m_expr(e), m_fn(fn), m_delay_factor(f), m_owner(owner) {}
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
constraint mk_choice_cnstr(expr const & m, choice_fn const & fn, delay_factor const & f,
                           bool owner, justification const & j) {
    lean_assert(is_meta(m));
    return constraint(new choice_constraint_cell(m, fn, f, owner, j));
}

expr const & cnstr_lhs_expr(constraint const & c) {
    lean_assert(is_eq_cnstr(c));
    return static_cast<eq_constraint_cell*>(c.raw())->m_lhs;
}
expr const & cnstr_rhs_expr(constraint const & c) {
    lean_assert(is_eq_cnstr(c));
    return static_cast<eq_constraint_cell*>(c.raw())->m_rhs;
}
level const & cnstr_lhs_level(constraint const & c) {
    lean_assert(is_level_eq_cnstr(c));
    return static_cast<level_constraint_cell*>(c.raw())->m_lhs;
}
level const & cnstr_rhs_level(constraint const & c) {
    lean_assert(is_level_eq_cnstr(c));
    return static_cast<level_constraint_cell*>(c.raw())->m_rhs;
}
expr const & cnstr_expr(constraint const & c) {
    lean_assert(is_choice_cnstr(c));
    return static_cast<choice_constraint_cell*>(c.raw())->m_expr;
}
choice_fn const & cnstr_choice_fn(constraint const & c) {
    lean_assert(is_choice_cnstr(c)); return static_cast<choice_constraint_cell*>(c.raw())->m_fn;
}
bool cnstr_on_demand(constraint const & c) {
    lean_assert(is_choice_cnstr(c));
    return static_cast<choice_constraint_cell*>(c.raw())->m_delay_factor.on_demand();
}
delay_factor const & cnstr_delay_factor_core(constraint const & c) {
    lean_assert(is_choice_cnstr(c));
    return static_cast<choice_constraint_cell*>(c.raw())->m_delay_factor;
}
unsigned cnstr_delay_factor(constraint const & c) {
    return cnstr_delay_factor_core(c).explict_value();
}
bool cnstr_is_owner(constraint const & c) {
    lean_assert(is_choice_cnstr(c)); return static_cast<choice_constraint_cell*>(c.raw())->m_owner;
}

constraint update_justification(constraint const & c, justification const & j) {
    switch (c.kind()) {
    case constraint_kind::Eq:
        return mk_eq_cnstr(cnstr_lhs_expr(c), cnstr_rhs_expr(c), j);
    case constraint_kind::LevelEq:
        return mk_level_eq_cnstr(cnstr_lhs_level(c), cnstr_rhs_level(c), j);
    case constraint_kind::Choice:
        return mk_choice_cnstr(cnstr_expr(c), cnstr_choice_fn(c),
                               static_cast<choice_constraint_cell*>(c.raw())->m_delay_factor,
                               cnstr_is_owner(c), j);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

void to_buffer(constraint_seq const & cs, justification const & j, buffer<constraint> & r) {
    return cs.for_each([&](constraint const & c) {
            r.push_back(update_justification(c, mk_composite1(c.get_justification(), j)));
        });
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
        out << "choice ";
        if (cnstr_on_demand(c))
            out << "[on-demand]";
        else if (cnstr_delay_factor(c) != 0)
            out << "[delayed:" << cnstr_delay_factor(c) << "] ";
        out << cnstr_expr(c);
        break;
    }
    return out;
}
}
void print(lean::constraint const & c) { std::cout << c << "\n"; }

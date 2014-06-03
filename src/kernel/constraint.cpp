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
struct eq_constraint_cell : public constraint_cell {
    expr m_lhs;
    expr m_rhs;
    eq_constraint_cell(expr const & lhs, expr const & rhs, justification const & j):
        constraint_cell(constraint_kind::Eq, hash(lhs.hash(), rhs.hash()), j),
        m_lhs(lhs), m_rhs(rhs) {}
};
struct level_constraint_cell : public constraint_cell {
    level m_lhs;
    level m_rhs;
    level_constraint_cell(level const & lhs, level const & rhs, justification const & j):
        constraint_cell(constraint_kind::Level, hash(hash(lhs), hash(rhs)), j),
        m_lhs(lhs), m_rhs(rhs) {}
};

void constraint_cell::dealloc() {
    switch (m_kind) {
    case constraint_kind::Eq:
        delete static_cast<eq_constraint_cell*>(this); break;
    case constraint_kind::Level:
        delete static_cast<level_constraint_cell*>(this); break;
    }
}

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
    return constraint(new eq_constraint_cell(lhs, rhs, j));
}
constraint mk_level_cnstr(level const & lhs, level const & rhs, justification const & j) {
    return constraint(new level_constraint_cell(lhs, rhs, j));
}

bool operator==(constraint const & c1, constraint const & c2) {
    if (c1.kind() != c2.kind() || c1.hash() != c2.hash())
        return false;
    switch (c1.kind()) {
    case constraint_kind::Eq:
        return cnstr_lhs_expr(c1) == cnstr_lhs_expr(c2) && cnstr_rhs_expr(c1) == cnstr_rhs_expr(c2);
    case constraint_kind::Level:
        return cnstr_lhs_level(c1) == cnstr_lhs_level(c2) && cnstr_rhs_level(c1) == cnstr_rhs_level(c2);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr const & cnstr_lhs_expr(constraint const & c) { lean_assert(is_eq_cnstr(c)); return static_cast<eq_constraint_cell*>(c.raw())->m_lhs; }
expr const & cnstr_rhs_expr(constraint const & c) { lean_assert(is_eq_cnstr(c)); return static_cast<eq_constraint_cell*>(c.raw())->m_rhs; }
level const & cnstr_lhs_level(constraint const & c) { lean_assert(is_level_cnstr(c)); return static_cast<level_constraint_cell*>(c.raw())->m_lhs; }
level const & cnstr_rhs_level(constraint const & c) { lean_assert(is_level_cnstr(c)); return static_cast<level_constraint_cell*>(c.raw())->m_rhs; }

constraint updt_eq_cnstr(constraint const & c, expr const & new_lhs, expr const & new_rhs, justification const & new_jst) {
    lean_assert(is_eq_cnstr(c));
    if (!is_eqp(cnstr_lhs_expr(c), new_lhs) || !is_eqp(cnstr_rhs_expr(c), new_rhs))
        return mk_eq_cnstr(new_lhs, new_rhs, new_jst);
    else
        return c;
}
constraint updt_eq_cnstr(constraint const & c, expr const & new_lhs, expr const & new_rhs) {
    return updt_eq_cnstr(c, new_lhs, new_rhs, c.get_justification());
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
        break;
    case constraint_kind::Level:
        out << cnstr_lhs_level(c) << " = " << cnstr_rhs_level(c);
        break;
    }
    return out;
}
}

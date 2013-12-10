/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/elaborator/elaborator_justification.h"

namespace lean {
// -------------------------
// Propagation justification
// -------------------------
propagation_justification::propagation_justification(unification_constraint const & c):
    m_constraint(c) {
}
propagation_justification::~propagation_justification() {
}
void propagation_justification::get_children(buffer<justification_cell*> & r) const {
    push_back(r, m_constraint.get_justification());
}
optional<expr> propagation_justification::get_main_expr() const {
    return none_expr();
}
format propagation_justification::pp_header(formatter const & fmt, options const & opts) const {
    format r;
    r += format(get_prop_name());
    r += compose(line(), get_constraint().pp(fmt, opts, nullptr, false));
    return r;
}

// -------------------------
// Unification failure (by cases)
// -------------------------
unification_failure_by_cases_justification::unification_failure_by_cases_justification(unification_constraint const & c, unsigned num, justification const * cs):
    unification_failure_justification(c),
    m_cases(cs, cs + num) {
}
unification_failure_by_cases_justification::~unification_failure_by_cases_justification() {
}
void unification_failure_by_cases_justification::get_children(buffer<justification_cell*> & r) const {
    push_back(r, get_constraint().get_justification());
    append(r, m_cases);
}

// -------------------------
// Substitution justification
// -------------------------
substitution_justification::substitution_justification(unification_constraint const & c, justification const & t):
    propagation_justification(c),
    m_assignment_justification(t) {
}
substitution_justification::~substitution_justification() {
}
void substitution_justification::get_children(buffer<justification_cell*> & r) const {
    propagation_justification::get_children(r);
    push_back(r, m_assignment_justification);
}

multi_substitution_justification::multi_substitution_justification(unification_constraint const & c, unsigned num, justification const * ts):
    propagation_justification(c),
    m_assignment_justifications(ts, ts + num) {
}
multi_substitution_justification::~multi_substitution_justification() {
}
void multi_substitution_justification::get_children(buffer<justification_cell*> & r) const {
    propagation_justification::get_children(r);
    append(r, m_assignment_justifications);
}

// -------------------------
// typeof metavar justification
// -------------------------
typeof_mvar_justification::typeof_mvar_justification(context const & ctx, expr const & m, expr const & tm, expr const & t, justification const & tr):
    m_context(ctx),
    m_mvar(m),
    m_typeof_mvar(tm),
    m_type(t),
    m_justification(tr) {
}
typeof_mvar_justification::~typeof_mvar_justification() {
}
format typeof_mvar_justification::pp_header(formatter const & fmt, options const & opts) const {
    format r;
    unsigned indent = get_pp_indent(opts);
    r += format("Propagate type,");
    {
        format body;
        body += fmt(m_context, m_mvar, false, opts);
        body += space();
        body += colon();
        body += nest(indent, compose(line(), fmt(m_context, m_typeof_mvar, false, opts)));
        r += nest(indent, compose(line(), body));
    }
    return group(r);
}
void typeof_mvar_justification::get_children(buffer<justification_cell*> & r) const {
    push_back(r, m_justification);
}

// -------------------------
// Next solution justification
// -------------------------
next_solution_justification::next_solution_justification(unsigned num, justification const * as):
    m_assumptions(as, as + num) {
}
next_solution_justification::~next_solution_justification() {
}
format next_solution_justification::pp_header(formatter const &, options const &) const {
    return format("next solution");
}
void next_solution_justification::get_children(buffer<justification_cell*> & r) const {
    append(r, m_assumptions);
}
optional<expr> next_solution_justification::get_main_expr() const {
    return none_expr();
}
}

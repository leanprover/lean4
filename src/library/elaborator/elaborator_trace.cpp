/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/elaborator/elaborator_trace.h"

namespace lean {
static void push_back(buffer<trace_cell*> & r, trace const & t) {
    if (t)
        r.push_back(t.raw());
}

template<typename T>
static void append(buffer<trace_cell*> & r, T const & s) {
    for (auto t : s)
        push_back(r, t);
}

// -------------------------
// Assumptions
// -------------------------
assumption_trace::assumption_trace(unsigned idx):m_idx(idx) {
}
void assumption_trace::get_children(buffer<trace_cell*> &) const {
}
expr const & assumption_trace::get_main_expr() const {
    return expr::null();
}
format assumption_trace::pp_header(formatter const &, options const &) const {
    return format{format("assumption"), space(), format(m_idx)};
}

// -------------------------
// Propagation trace
// -------------------------
propagation_trace::propagation_trace(unification_constraint const & c):
    m_constraint(c) {
}
propagation_trace::~propagation_trace() {
}
void propagation_trace::get_children(buffer<trace_cell*> & r) const {
    push_back(r, m_constraint.get_trace());
}
expr const & propagation_trace::get_main_expr() const {
    return expr::null();
}
format propagation_trace::pp_header(formatter const & fmt, options const & opts) const {
    format r;
    r += format(get_prop_name());
    r += compose(line(), get_constraint().pp(fmt, opts, nullptr, false));
    return r;
}

// -------------------------
// Unification failure (by cases)
// -------------------------
unification_failure_by_cases_trace::unification_failure_by_cases_trace(unification_constraint const & c, unsigned num, trace const * cs):
    unification_failure_trace(c),
    m_cases(cs, cs + num) {
}
unification_failure_by_cases_trace::~unification_failure_by_cases_trace() {
}
void unification_failure_by_cases_trace::get_children(buffer<trace_cell*> & r) const {
    push_back(r, get_constraint().get_trace());
    append(r, m_cases);
}

// -------------------------
// Substitution trace
// -------------------------
substitution_trace::substitution_trace(unification_constraint const & c, trace const & t):
    propagation_trace(c),
    m_assignment_trace(t) {
}
substitution_trace::~substitution_trace() {
}
void substitution_trace::get_children(buffer<trace_cell*> & r) const {
    propagation_trace::get_children(r);
    push_back(r, m_assignment_trace);
}

multi_substitution_trace::multi_substitution_trace(unification_constraint const & c, unsigned num, trace const * ts):
    propagation_trace(c),
    m_assignment_traces(ts, ts + num) {
}
multi_substitution_trace::~multi_substitution_trace() {
}
void multi_substitution_trace::get_children(buffer<trace_cell*> & r) const {
    propagation_trace::get_children(r);
    append(r, m_assignment_traces);
}

// -------------------------
// typeof metavar trace
// -------------------------
typeof_mvar_trace::typeof_mvar_trace(context const & ctx, expr const & m, expr const & tm, expr const & t, trace const & tr):
    m_context(ctx),
    m_mvar(m),
    m_typeof_mvar(tm),
    m_type(t),
    m_trace(tr) {
}
typeof_mvar_trace::~typeof_mvar_trace() {
}
format typeof_mvar_trace::pp_header(formatter const & fmt, options const & opts) const {
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
void typeof_mvar_trace::get_children(buffer<trace_cell*> & r) const {
    push_back(r, m_trace);
}

// -------------------------
// Synthesis trace objects
// -------------------------
synthesis_trace::synthesis_trace(context const & ctx, expr const & mvar, expr const & type, unsigned num, trace const * substs):
    m_context(ctx),
    m_mvar(mvar),
    m_type(type),
    m_substitution_traces(substs, substs + num) {
}
synthesis_trace::~synthesis_trace() {
}
format synthesis_trace::pp_header(formatter const & fmt, options const & opts) const {
    format r;
    r += format(get_label());
    r += space();
    r += fmt(m_context, m_mvar, false, opts);
    unsigned indent = get_pp_indent(opts);
    r += nest(indent, compose(line(), fmt(m_context, m_type, true, opts)));
    return r;
}
void synthesis_trace::get_children(buffer<trace_cell*> & r) const {
    append(r, m_substitution_traces);
}
expr const & synthesis_trace::get_main_expr() const {
    return m_mvar;
}

char const * synthesis_failure_trace::get_label() const {
    return "Failed to synthesize expression of type for";
}
synthesis_failure_trace::synthesis_failure_trace(context const & ctx, expr const & mvar, expr const & type, trace const & tr, unsigned num, trace const * substs):
    synthesis_trace(ctx, mvar, type, num, substs),
    m_trace(tr) {
}
synthesis_failure_trace::~synthesis_failure_trace() {
}
void synthesis_failure_trace::get_children(buffer<trace_cell*> & r) const {
    synthesis_trace::get_children(r);
    push_back(r, m_trace);
}

char const * synthesized_assignment_trace::get_label() const {
    return "Synthesized assignment for";
}

// -------------------------
// Next solution trace
// -------------------------
next_solution_trace::next_solution_trace(unsigned num, trace const * as):
    m_assumptions(as, as + num) {
}
next_solution_trace::~next_solution_trace() {
}
format next_solution_trace::pp_header(formatter const &, options const &) const {
    return format("next solution");
}
void next_solution_trace::get_children(buffer<trace_cell*> & r) const {
    append(r, m_assumptions);
}
expr const & next_solution_trace::get_main_expr() const {
    return expr::null();
}
}

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
unification_constraint_cell::~unification_constraint_cell() {
}
void unification_constraint_cell::dealloc() {
    delete this;
}

static format add_context(formatter const & fmt, options const & opts, context const & ctx, format const & body) {
    bool unicode     = get_pp_unicode(opts);
    format ctx_fmt   = fmt(ctx, opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    return group(format{ctx_fmt, space(), turnstile, line(), body});
}

static format add_trace(formatter const & fmt, options const & opts, format const & body, trace const & tr, pos_info_provider const * p, bool include_trace) {
    if (tr && include_trace) {
        unsigned indent  = get_pp_indent(opts);
        return format{body, line(), format("Trace:"), nest(indent, compose(line(), tr.pp(fmt, opts, p)))};
    } else {
        return body;
    }
}

static format mk_binary(formatter const & fmt, options const & opts, context const & ctx, expr const & lhs, expr const & rhs, format const & op) {
    format lhs_fmt  = fmt(ctx, lhs, false, opts);
    format rhs_fmt  = fmt(ctx, rhs, false, opts);
    return group(format{lhs_fmt, space(), op, line(), rhs_fmt});
}

static format mk_unification_op(options const & opts) {
    bool unicode = get_pp_unicode(opts);
    return unicode ? format("\u2248") /* ≈ */ : format("=?=");
}

unification_constraint_eq::unification_constraint_eq(context const & c, expr const & lhs, expr const & rhs, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Eq, c, t),
    m_lhs(lhs),
    m_rhs(rhs) {
}

unification_constraint_eq::~unification_constraint_eq() {
}

format unification_constraint_eq::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_trace) const {
    format op   = mk_unification_op(opts);
    format body = mk_binary(fmt, opts, m_ctx, m_lhs, m_rhs, op);
    body = add_context(fmt, opts, m_ctx, body);
    return add_trace(fmt, opts, body, m_trace, p, include_trace);
}

unification_constraint_convertible::unification_constraint_convertible(context const & c, expr const & from, expr const & to, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Convertible, c, t),
    m_from(from),
    m_to(to) {
}

unification_constraint_convertible::~unification_constraint_convertible() {
}

format unification_constraint_convertible::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_trace) const {
    bool unicode = get_pp_unicode(opts);
    format op    = unicode ? format("\u227A") /* ≺ */ : format("<<");
    format body  = mk_binary(fmt, opts, m_ctx, m_from, m_to, op);
    body = add_context(fmt, opts, m_ctx, body);
    return add_trace(fmt, opts, body, m_trace, p, include_trace);
}

unification_constraint_max::unification_constraint_max(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Max, c, t),
    m_lhs1(lhs1),
    m_lhs2(lhs2),
    m_rhs(rhs) {
}

unification_constraint_max::~unification_constraint_max() {
}

format unification_constraint_max::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_trace) const {
    format op       = mk_unification_op(opts);
    format lhs1_fmt = fmt(m_ctx, m_lhs1, false, opts);
    format lhs2_fmt = fmt(m_ctx, m_lhs2, false, opts);
    format rhs_fmt  = fmt(m_ctx, m_rhs, false, opts);
    format body     = group(format{format("max"), lp(), lhs1_fmt, comma(), nest(4, compose(line(), lhs2_fmt)), space(), op, line(), rhs_fmt});
    body = add_context(fmt, opts, m_ctx, body);
    return add_trace(fmt, opts, body, m_trace, p, include_trace);
}

unification_constraint_choice::unification_constraint_choice(context const & c, expr const & mvar, unsigned num, trace const & t):
    unification_constraint_cell(unification_constraint_kind::Choice, c, t),
    m_mvar(mvar),
    m_num_choices(num) {
}

unification_constraint_choice::~unification_constraint_choice() {
}

format unification_constraint_choice::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_trace) const {
    bool unicode    = get_pp_unicode(opts);
    format m_fmt    = fmt(m_ctx, m_mvar, false, opts);
    format eq_op    = mk_unification_op(opts);
    format or_op    = unicode ? format("\u2295") : format("OR");
    format body;
    for (unsigned i = 0; i < m_num_choices; i++) {
        body += group(paren(format{m_fmt, space(), eq_op, compose(line(), fmt(m_ctx, m_choices[i], false, opts))}));
        if (i + 1 < m_num_choices)
            body += format{space(), or_op, line()};
    }
    body = group(body);
    body = add_context(fmt, opts, m_ctx, body);
    return add_trace(fmt, opts, body, m_trace, p, include_trace);
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

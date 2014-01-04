/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/unification_constraint.h"
#include "kernel/metavar.h"

namespace lean {
unification_constraint_cell::unification_constraint_cell(unification_constraint_kind k, context const & c, justification const & j):
    m_kind(k), m_ctx(c), m_justification(j), m_rc(1) {
}
unification_constraint_cell::~unification_constraint_cell() {
}
void unification_constraint_cell::dealloc() {
    delete this;
}

static format add_context(formatter const & fmt, options const & opts, context const & ctx, format const & body, optional<metavar_env> const & menv) {
    bool unicode     = get_pp_unicode(opts);
    format ctx_fmt   = fmt(instantiate_metavars(menv, ctx), opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    return group(format{ctx_fmt, space(), turnstile, line(), body});
}

static format add_justification(formatter const & fmt, options const & opts, format const & body, justification const & jst, pos_info_provider const * p, bool include_justification, optional<metavar_env> const & menv) {
    if (jst && include_justification) {
        unsigned indent  = get_pp_indent(opts);
        return format{body, line(), format("Justification:"), nest(indent, compose(line(), jst.pp(fmt, opts, p, true, menv)))};
    } else {
        return body;
    }
}

static format mk_binary(formatter const & fmt, options const & opts, context const & ctx, expr const & lhs, expr const & rhs, format const & op,
                        optional<metavar_env> const & menv) {
    format lhs_fmt  = fmt(ctx, instantiate_metavars(menv, lhs), false, opts);
    format rhs_fmt  = fmt(ctx, instantiate_metavars(menv, rhs), false, opts);
    return group(format{lhs_fmt, space(), op, line(), rhs_fmt});
}

static format mk_unification_op(options const & opts) {
    bool unicode = get_pp_unicode(opts);
    return unicode ? format("\u2248") /* ≈ */ : format("=?=");
}

unification_constraint_eq::unification_constraint_eq(context const & c, expr const & lhs, expr const & rhs, justification const & j):
    unification_constraint_cell(unification_constraint_kind::Eq, c, j),
    m_lhs(lhs),
    m_rhs(rhs) {
}

unification_constraint_eq::~unification_constraint_eq() {
}

format unification_constraint_eq::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification,
                                     optional<metavar_env> const & menv) const {
    format op   = mk_unification_op(opts);
    format body = mk_binary(fmt, opts, m_ctx, m_lhs, m_rhs, op, menv);
    body = add_context(fmt, opts, m_ctx, body, menv);
    return add_justification(fmt, opts, body, m_justification, p, include_justification, menv);
}

unification_constraint_convertible::unification_constraint_convertible(context const & c, expr const & from, expr const & to, justification const & j):
    unification_constraint_cell(unification_constraint_kind::Convertible, c, j),
    m_from(from),
    m_to(to) {
}

unification_constraint_convertible::~unification_constraint_convertible() {
}

format unification_constraint_convertible::pp(formatter const & fmt, options const & opts, pos_info_provider const * p,
                                              bool include_justification, optional<metavar_env> const & menv) const {
    bool unicode = get_pp_unicode(opts);
    format op    = unicode ? format("\u227A") /* ≺ */ : format("<<");
    format body  = mk_binary(fmt, opts, m_ctx, m_from, m_to, op, menv);
    body = add_context(fmt, opts, m_ctx, body, menv);
    return add_justification(fmt, opts, body, m_justification, p, include_justification, menv);
}

unification_constraint_max::unification_constraint_max(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, justification const & j):
    unification_constraint_cell(unification_constraint_kind::Max, c, j),
    m_lhs1(lhs1),
    m_lhs2(lhs2),
    m_rhs(rhs) {
}

unification_constraint_max::~unification_constraint_max() {
}

format unification_constraint_max::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification,
                                      optional<metavar_env> const & menv) const {
    format op       = mk_unification_op(opts);
    format lhs1_fmt = fmt(m_ctx, instantiate_metavars(menv, m_lhs1), false, opts);
    format lhs2_fmt = fmt(m_ctx, instantiate_metavars(menv, m_lhs2), false, opts);
    format rhs_fmt  = fmt(m_ctx, instantiate_metavars(menv, m_rhs), false, opts);
    format body     = group(format{format("max"), lp(), lhs1_fmt, comma(), nest(4, compose(line(), lhs2_fmt)), rp(), space(), op, line(), rhs_fmt});
    body = add_context(fmt, opts, m_ctx, body, menv);
    return add_justification(fmt, opts, body, m_justification, p, include_justification, menv);
}

unification_constraint_choice::unification_constraint_choice(context const & c, expr const & mvar, unsigned num, expr const * choices, justification const & j):
    unification_constraint_cell(unification_constraint_kind::Choice, c, j),
    m_mvar(mvar),
    m_choices(choices, choices + num) {
}

unification_constraint_choice::~unification_constraint_choice() {
}

format unification_constraint_choice::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification,
                                         optional<metavar_env> const & menv) const {
    bool unicode    = get_pp_unicode(opts);
    format m_fmt    = fmt(m_ctx, m_mvar, false, opts);
    format eq_op    = mk_unification_op(opts);
    format or_op    = unicode ? format("\u2295") : format("OR");
    format body;
    for (unsigned i = 0; i < m_choices.size(); i++) {
        body += group(paren(format{m_fmt, space(), eq_op, compose(line(), fmt(m_ctx, instantiate_metavars(menv, m_choices[i]), false, opts))}));
        if (i + 1 < m_choices.size())
            body += format{space(), or_op, line()};
    }
    body = group(body);
    body = add_context(fmt, opts, m_ctx, body, menv);
    return add_justification(fmt, opts, body, m_justification, p, include_justification, menv);
}

format unification_constraint::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification,
                                  optional<metavar_env> const & menv) const {
    return m_ptr->pp(fmt, opts, p, include_justification, menv);
}

format unification_constraint::pp(formatter const & fmt, options const & opts, pos_info_provider const * p, bool include_justification) const {
    return pp(fmt, opts, p, include_justification, optional<metavar_env>());
}

unification_constraint mk_eq_constraint(context const & c, expr const & lhs, expr const & rhs, justification const & j) {
    return unification_constraint(new unification_constraint_eq(c, lhs, rhs, j));
}

unification_constraint mk_convertible_constraint(context const & c, expr const & from, expr const & to, justification const & j) {
    return unification_constraint(new unification_constraint_convertible(c, from, to, j));
}

unification_constraint mk_max_constraint(context const & c, expr const & lhs1, expr const & lhs2, expr const & rhs, justification const & j) {
    return unification_constraint(new unification_constraint_max(c, lhs1, lhs2, rhs, j));
}

unification_constraint mk_choice_constraint(context const & c, expr const & mvar, unsigned num, expr const * choices, justification const & j) {
    return unification_constraint(new unification_constraint_choice(c, mvar, num, choices, j));
}

unification_constraint mk_choice_constraint(context const & c, expr const & mvar, std::initializer_list<expr> const & choices, justification const & j) {
    return mk_choice_constraint(c, mvar, choices.size(), choices.begin(), j);
}
}

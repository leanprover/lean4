/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/tactic/congruence/congruence_closure.h"
#include "library/tactic/congruence/theory_ac.h"

namespace lean {
theory_ac::theory_ac(congruence_closure & cc, state & s):
    m_ctx(cc.ctx()),
    m_cc(cc),
    m_state(s),
    m_ac_manager(cc.ctx()) {
}

theory_ac::~theory_ac() {
}

optional<expr> theory_ac::is_ac(expr const & e) {
    optional<expr> assoc_pr = m_ac_manager.is_assoc(e);
    if (!assoc_pr) return none_expr();
    optional<expr> comm_pr  = m_ac_manager.is_comm(e);
    if (!comm_pr) return none_expr();
    expr const & op = app_fn(app_fn(e));
    if (auto it = m_state.m_can_ops.find(op))
        return some_expr(*it);
    optional<expr> found_op;
    m_state.m_op_info.for_each([&](expr const & c_op, expr_pair const &) {
            if (!found_op && m_ctx.relaxed_is_def_eq(op, c_op))
                found_op = c_op;
        });
    if (found_op) {
        m_state.m_can_ops.insert(op, *found_op);
        return found_op;
    } else {
        m_state.m_can_ops.insert(op, op);
        m_state.m_op_info.insert(op, mk_pair(*assoc_pr, *comm_pr));
        return some_expr(op);
    }
}

optional<expr> theory_ac::internalize(expr const & e, optional<expr> const & parent) {
    auto op = is_ac(e);
    if (!op) return none_expr();
    optional<expr> parent_op;
    if (parent) parent_op = is_ac(*parent);
    if (parent_op && *op == *parent_op) return none_expr();

    // TODO(Leo): compute representative and initialize
    expr rep = e;

    lean_trace(name({"cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               tout() << "new term: " << rep << "\n";);
    return some_expr(rep);
}

void theory_ac::add_eq(expr const & e1, expr const & e2) {
    lean_trace(name({"cc", "ac"}), scope_trace_env s(m_ctx.env(), m_ctx);
               tout() << "new eq: " << e1 << " = " << e2 << "\n";);
    // TODO(Leo)
}

void initialize_theory_ac() {
    register_trace_class(name({"cc", "ac"}));
}

void finalize_theory_ac() {
}
}

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/list_fn.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/locals.h"
#include "library/type_context.h"
#include "library/defeq_canonizer.h"

namespace lean {
defeq_canonizer::defeq_canonizer(type_context_old & ctx, state & s):
    m_ctx(ctx), m_state(s) {
}

optional<name> defeq_canonizer::get_head_symbol(expr type) {
    type    = m_ctx.whnf(type);
    expr const & fn = get_app_fn(type);
    if (is_constant(fn)) {
        return optional<name>(const_name(fn));
    } else if (is_pi(type)) {
        type_context_old::tmp_locals locals(m_ctx);
        expr l = locals.push_local_from_binding(type);
        return get_head_symbol(instantiate(binding_body(type), l));
    } else {
        return optional<name>();
    }
}

optional<expr> defeq_canonizer::find_defeq(name const & h, expr const & e) {
    list<expr> const * lst = m_state.m_M.find(h);
    if (!lst) return none_expr();
    for (expr const & e1 : *lst) {
        if (locals_subset(e1, e) && m_ctx.is_def_eq(e1, e))
            return some_expr(e1);
    }
    return none_expr();
}

void defeq_canonizer::replace_C(expr const & e1, expr const & e2) {
    m_state.m_C.insert(e1, e2);
    if (m_updated)
        *m_updated = true;
}

void defeq_canonizer::insert_C(expr const & e1, expr const & e2) {
    m_state.m_C.insert(e1, e2);
}

void defeq_canonizer::insert_M(name const & h, expr const & e) {
    list<expr> const * lst = m_state.m_M.find(h);
    if (lst) {
        m_state.m_M.insert(h, cons(e, *lst));
    } else {
        m_state.m_M.insert(h, to_list(e));
    }
}

void defeq_canonizer::replace_M(name const & h, expr const & e, expr const & new_e) {
    list<expr> const * lst = m_state.m_M.find(h);
    lean_assert(lst);
    m_state.m_M.insert(h, cons(new_e, remove(*lst, e)));
}

expr defeq_canonizer::canonize_core(expr const & e) {
    if (auto it = m_state.m_C.find(e)) {
        expr e1 = *it;
        if (e1 == e)
            return e;
        expr e2 = canonize_core(e1);
        if (e2 != e1) {
            replace_C(e, e2);
        }
        return e2;
    }
    expr e_type  = m_ctx.infer(e);
    optional<name> h = get_head_symbol(e_type);
    if (!h) {
        /* canonization is not support for type of e */
        insert_C(e, e);
        return e;
    } else if (optional<expr> new_e = find_defeq(*h, e)) {
        if (get_weight(e) < get_weight(*new_e) && locals_subset(e, *new_e)) {
            replace_C(*new_e, e);
            replace_M(*h, *new_e, e);
            insert_C(e, e);
            return e;
        } else {
            insert_C(e, *new_e);
            return *new_e;
        }
    } else {
        insert_C(e, e);
        insert_M(*h, e);
        return e;
    }
}

static void trace(type_context_old & ctx, expr const & e, expr const & r) {
    lean_trace("defeq_canonizer", scope_trace_env _(ctx.env(), ctx); tout() << "\n" << e << "\n==>\n" << r << "\n";);
}

expr defeq_canonizer::canonize(expr const & e, bool & updated) {
    type_context_old::transparency_scope scope(m_ctx, transparency_mode::Instances);
    m_updated = &updated;
    expr r = canonize_core(e);
    trace(m_ctx, e, r);
    return r;
}

expr defeq_canonizer::canonize(expr const & e) {
    type_context_old::transparency_scope scope(m_ctx, transparency_mode::Instances);
    m_updated = nullptr;
    expr r = canonize_core(e);
    trace(m_ctx, e, r);
    return r;
}

void initialize_defeq_canonizer() {
    register_trace_class("defeq_canonizer");
}

void finalize_defeq_canonizer() {
}
}

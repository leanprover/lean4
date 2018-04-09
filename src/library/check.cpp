/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr_sets.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/type_context.h"

namespace lean {
struct check_fn {
    type_context_old &   m_ctx;
    expr_set             m_visited;

    void visit_constant(expr const & e) {
        declaration d = m_ctx.env().get(const_name(e));
        if (d.get_num_univ_params() != length(const_levels(e))) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "incorrect of universe levels at " << e << "\n";);
            throw exception("check failed, incorrect number of universe levels "
                            "(use 'set_option trace.check true' for additional details)");
        }
    }

    void visit_macro(expr const & e) {
        for (unsigned i = 0; i < macro_num_args(e); i++)
            visit(macro_arg(e, i));
    }

    void ensure_type(expr const & e) {
        expr S = m_ctx.relaxed_whnf(m_ctx.infer(e));
        if (is_sort(S)) return;
        if (is_metavar(S)) {
            level u = m_ctx.mk_univ_metavar_decl();
            if (m_ctx.is_def_eq(S, mk_sort(u)))
                return;
        }
        lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                   tout() << "type expected at " << e << "\n";);
        throw exception("check failed, type expected "
                        "(use 'set_option trace.check true' for additional details)");
    }

    void visit_binding(expr const & e, bool is_pi) {
        type_context_old::tmp_locals locals(m_ctx);
        expr it = e;
        while (it.kind() == e.kind()) {
            expr d = instantiate_rev(binding_domain(it), locals.size(), locals.data());
            visit(d);
            locals.push_local(binding_name(it), d, binding_info(it));
            ensure_type(d);
            it = binding_body(it);
        }
        expr b = instantiate_rev(it, locals.size(), locals.data());
        visit(b);
        if (is_pi)
            ensure_type(b);
    }

    void visit_lambda(expr const & e) {
        visit_binding(e, false);
    }

    void visit_pi(expr const & e) {
        visit_binding(e, true);
    }

    void visit_let(expr const & e) {
        visit(let_value(e));
        visit(let_type(e));
        expr v_type = m_ctx.infer(let_value(e));
        if (!m_ctx.relaxed_is_def_eq(let_type(e), v_type)) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "type mismatch at let binder\n  " << e << "\n";);
            throw exception("check failed, type mismatch at let binder "
                            "(use 'set_option trace.check true' for additional details)");
        }
        /* Improve performance if bottleneck */
        type_context_old::tmp_locals locals(m_ctx);
        expr local = locals.push_local_from_let(e);
        visit(instantiate(let_body(e), local));
    }

    void visit_app(expr const & e) {
        visit(app_fn(e));
        visit(app_arg(e));
        expr f_type = m_ctx.relaxed_whnf(m_ctx.infer(app_fn(e)));
        if (!is_pi(f_type)) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "function expected at\n  " << e << "\ntype\n  " << f_type << "\n";);
            throw exception("check failed, function expected (use 'set_option trace.check true' for additional details)");
        }
        expr a_type = m_ctx.infer(app_arg(e));
        expr d_type = binding_domain(f_type);
        if (!m_ctx.relaxed_is_def_eq(a_type, d_type)) {
            lean_trace("check", scope_trace_env _(m_ctx.env(), m_ctx);
                       tout() << "application type mismatch at\n  " << e << "\nargument type\n  "
                       << a_type << "\nexpected type\n  " << d_type;);
            throw exception("check failed, application type mismatch "
                            "(use 'set_option trace.check true' for additional details)");
        }
    }

    void visit(expr const & e) {
        if (m_visited.find(e) != m_visited.end())
            return;
        m_visited.insert(e);
        switch (e.kind()) {
        case expr_kind::Local:
        case expr_kind::Meta:
        case expr_kind::Sort:
            break; /* do nothing */
        case expr_kind::Constant:
            return visit_constant(e);
        case expr_kind::Var:
            lean_unreachable();  // LCOV_EXCL_LINE
        case expr_kind::Macro:
            return visit_macro(e);
        case expr_kind::Lambda:
            return visit_lambda(e);
        case expr_kind::Pi:
            return visit_pi(e);
        case expr_kind::App:
            return visit_app(e);
        case expr_kind::Let:
            return visit_let(e);
        }
    }

public:
    check_fn(type_context_old & ctx):m_ctx(ctx) {}
    void operator()(expr const & e) { return visit(e); }
};

void check(type_context_old & ctx, expr const & e) {
    metavar_context mctx = ctx.mctx();
    check_fn checker(ctx);
    checker(e);
    ctx.set_mctx(mctx);
}

void initialize_check() {
    register_trace_class("check");
}

void finalize_check() {
}
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include "util/interrupt.h"
#include "util/freset.h"
#include "kernel/replace_visitor.h"

namespace lean {
expr replace_visitor::visit_sort(expr const & e, context const &) { lean_assert(is_sort(e)); return e; }
expr replace_visitor::visit_var(expr const & e, context const &) { lean_assert(is_var(e)); return e; }
expr replace_visitor::visit_constant(expr const & e, context const &) { lean_assert(is_constant(e)); return e; }
expr replace_visitor::visit_mlocal(expr const & e, context const & ctx) {
    lean_assert(is_mlocal(e));
    return update_mlocal(e, visit(mlocal_type(e), ctx));
}
expr replace_visitor::visit_meta(expr const & e, context const & ctx) { return visit_mlocal(e, ctx); }
expr replace_visitor::visit_local(expr const & e, context const & ctx) { return visit_mlocal(e, ctx); }
expr replace_visitor::visit_app(expr const & e, context const & ctx) {
    lean_assert(is_app(e));
    return update_app(e, visit(app_fn(e), ctx), visit(app_arg(e), ctx));
}
expr replace_visitor::visit_binder(expr const & e, context const & ctx) {
    lean_assert(is_binder(e));
    expr new_d = visit(binder_domain(e), ctx);
    freset<cache> reset(m_cache);
    expr new_b = visit(binder_body(e), extend(ctx, binder_name(e), new_d));
    return update_binder(e, new_d, new_b);
}
expr replace_visitor::visit_lambda(expr const & e, context const & ctx) { return visit_binder(e, ctx); }
expr replace_visitor::visit_pi(expr const & e, context const & ctx) { return visit_binder(e, ctx); }
expr replace_visitor::visit_let(expr const & e, context const & ctx) {
    lean_assert(is_let(e));
    expr new_t = visit(let_type(e), ctx);
    expr new_v = visit(let_value(e), ctx);
    freset<cache> reset(m_cache);
    expr new_b = visit(let_body(e), extend(ctx, let_name(e), new_t));
    return update_let(e, new_t, new_v, new_b);
}
expr replace_visitor::visit_macro(expr const & e, context const & ctx) {
    lean_assert(is_macro(e));
    buffer<expr> new_args;
    for (unsigned i = 0; i < macro_num_args(e); i++)
        new_args.push_back(visit(macro_arg(e, i), ctx));
    return update_macro(e, new_args.size(), new_args.data());
}
expr replace_visitor::save_result(expr const & e, expr && r, bool shared) {
    if (shared)
        m_cache.insert(std::make_pair(e, r));
    return r;
}
expr replace_visitor::visit(expr const & e, context const & ctx) {
    check_system("expression replacer");
    bool shared = false;
    if (is_shared(e)) {
        shared = true;
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;
    }

    switch (e.kind()) {
    case expr_kind::Sort:      return save_result(e, visit_sort(e, ctx), shared);
    case expr_kind::Macro:     return save_result(e, visit_macro(e, ctx), shared);
    case expr_kind::Constant:  return save_result(e, visit_constant(e, ctx), shared);
    case expr_kind::Var:       return save_result(e, visit_var(e, ctx), shared);
    case expr_kind::Meta:      return save_result(e, visit_meta(e, ctx), shared);
    case expr_kind::Local:     return save_result(e, visit_local(e, ctx), shared);
    case expr_kind::App:       return save_result(e, visit_app(e, ctx), shared);
    case expr_kind::Lambda:    return save_result(e, visit_lambda(e, ctx), shared);
    case expr_kind::Pi:        return save_result(e, visit_pi(e, ctx), shared);
    case expr_kind::Let:       return save_result(e, visit_let(e, ctx), shared);
    }

    lean_unreachable(); // LCOV_EXCL_LINE
}
}

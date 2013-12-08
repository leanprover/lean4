/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include "util/interrupt.h"
#include "kernel/replace_visitor.h"

namespace lean {
expr replace_visitor::visit_type(expr const & e, context const &) { lean_assert(is_type(e)); return e; }
expr replace_visitor::visit_value(expr const & e, context const &) { lean_assert(is_value(e)); return e; }
expr replace_visitor::visit_var(expr const & e, context const &) { lean_assert(is_var(e)); return e; }
expr replace_visitor::visit_metavar(expr const & e, context const &) { lean_assert(is_metavar(e)); return e; }
expr replace_visitor::visit_constant(expr const & e, context const & ctx) {
    lean_assert(is_constant(e));
    return update_const(e, visit(const_type(e), ctx));
}
expr replace_visitor::visit_app(expr const & e, context const & ctx) {
    lean_assert(is_app(e));
    return update_app(e, [&](expr const & c) { return visit(c, ctx); });
}
expr replace_visitor::visit_eq(expr const & e, context const & ctx) {
    lean_assert(is_eq(e));
    return update_eq(e, [&](expr const & l, expr const & r) { return std::make_pair(visit(l, ctx), visit(r, ctx)); });
}
expr replace_visitor::visit_abst(expr const & e, context const & ctx) {
    lean_assert(is_abstraction(e));
    return update_abst(e, [&](expr const & t, expr const & b) {
            expr new_t = visit(t, ctx);
            {
                cache::mk_scope sc(m_cache);
                expr new_b = visit(b, extend(ctx, abst_name(e), new_t));
                return std::make_pair(new_t, new_b);
            }
        });
}
expr replace_visitor::visit_lambda(expr const & e, context const & ctx) {
    lean_assert(is_lambda(e));
    return visit_abst(e, ctx);
}
expr replace_visitor::visit_pi(expr const & e, context const & ctx) {
    lean_assert(is_pi(e));
    return visit_abst(e, ctx);
}

expr replace_visitor::visit_let(expr const & e, context const & ctx) {
    lean_assert(is_let(e));
    return update_let(e, [&](optional<expr> const & t, expr const & v, expr const & b) {
            optional<expr> new_t = visit(t, ctx);
            expr new_v = visit(v, ctx);
            {
                cache::mk_scope sc(m_cache);
                expr new_b = visit(b, extend(ctx, let_name(e), new_t, new_v));
                return std::make_tuple(new_t, new_v, new_b);
            }
        });
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
    case expr_kind::Type:      return save_result(e, visit_type(e, ctx), shared);
    case expr_kind::Value:     return save_result(e, visit_value(e, ctx), shared);
    case expr_kind::Constant:  return save_result(e, visit_constant(e, ctx), shared);
    case expr_kind::Var:       return save_result(e, visit_var(e, ctx), shared);
    case expr_kind::MetaVar:   return save_result(e, visit_metavar(e, ctx), shared);
    case expr_kind::App:       return save_result(e, visit_app(e, ctx), shared);
    case expr_kind::Eq:        return save_result(e, visit_eq(e, ctx), shared);
    case expr_kind::Lambda:    return save_result(e, visit_lambda(e, ctx), shared);
    case expr_kind::Pi:        return save_result(e, visit_pi(e, ctx), shared);
    case expr_kind::Let:       return save_result(e, visit_let(e, ctx), shared);
    }

    lean_unreachable(); // LCOV_EXCL_LINE
}
optional<expr> replace_visitor::visit(optional<expr> const & e, context const & ctx) {
    if (e)
        return some_expr(visit(*e, ctx));
    else
        return none_expr();
}
}

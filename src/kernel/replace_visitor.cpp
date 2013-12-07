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
    if (const_type(e)) {
        return update_const(e, visit(const_type(e), ctx));
    } else {
        return e;
    }
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
            expr new_b;
            {
                cache::mk_scope sc(m_cache);
                new_b = visit(b, extend(ctx, abst_name(e), new_t));
            }
            return std::make_pair(new_t, new_b);
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
    return update_let(e, [&](expr const & t, expr const & v, expr const & b) {
            expr new_t = t ? visit(t, ctx) : expr();
            expr new_v = visit(v, ctx);
            expr new_b;
            {
                cache::mk_scope sc(m_cache);
                new_b = visit(b, extend(ctx, let_name(e), new_t, new_v));
            }
            return std::make_tuple(new_t, new_v, new_b);
        });
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

    expr r;
    switch (e.kind()) {
    case expr_kind::Type:      r = visit_type(e, ctx); break;
    case expr_kind::Value:     r = visit_value(e, ctx); break;
    case expr_kind::Constant:  r = visit_constant(e, ctx); break;
    case expr_kind::Var:       r = visit_var(e, ctx); break;
    case expr_kind::MetaVar:   r = visit_metavar(e, ctx); break;
    case expr_kind::App:       r = visit_app(e, ctx); break;
    case expr_kind::Eq:        r = visit_eq(e, ctx); break;
    case expr_kind::Lambda:    r = visit_lambda(e, ctx); break;
    case expr_kind::Pi:        r = visit_pi(e, ctx); break;
    case expr_kind::Let:       r = visit_let(e, ctx); break;
    }

    if (shared)
        m_cache.insert(std::make_pair(e, r));

    return r;
}
}

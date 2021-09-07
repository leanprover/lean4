/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include "runtime/interrupt.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/replace_visitor.h"

namespace lean {
expr replace_visitor::visit_sort(expr const & e) { lean_assert(is_sort(e)); return e; }
expr replace_visitor::visit_var(expr const & e) { lean_assert(is_var(e)); return e; }
expr replace_visitor::visit_lit(expr const & e) { lean_assert(is_lit(e)); return e; }
expr replace_visitor::visit_constant(expr const & e) { lean_assert(is_constant(e)); return e; }
expr replace_visitor::visit_meta(expr const & e) { lean_assert(is_mvar(e)); return e; }
expr replace_visitor::visit_fvar(expr const & e) { lean_assert(is_fvar(e)); return e; }
expr replace_visitor::visit_mdata(expr const & e) {
    return update_mdata(e, visit(mdata_expr(e)));
}
expr replace_visitor::visit_proj(expr const & e) {
    return update_proj(e, visit(proj_expr(e)));
}
expr replace_visitor::visit_app(expr const & e) {
    lean_assert(is_app(e));
    expr new_fn  = visit(app_fn(e));
    expr new_arg = visit(app_arg(e));
    return update_app(e, new_fn, new_arg);
}
expr replace_visitor::visit_binding(expr const & e) {
    lean_assert(is_binding(e));
    expr new_d = visit(binding_domain(e));
    expr new_b = visit(binding_body(e));
    return update_binding(e, new_d, new_b);
}
expr replace_visitor::visit_lambda(expr const & e) { return visit_binding(e); }
expr replace_visitor::visit_pi(expr const & e) { return visit_binding(e); }
expr replace_visitor::visit_let(expr const & e) {
    lean_assert(is_let(e));
    expr new_t = visit(let_type(e));
    expr new_v = visit(let_value(e));
    expr new_b = visit(let_body(e));
    return update_let(e, new_t, new_v, new_b);
}
expr replace_visitor::save_result(expr const & e, expr && r, bool shared) {
    if (shared)
        m_cache.insert(std::make_pair(e, r));
    return expr(r);
}
expr replace_visitor::visit(expr const & e) {
    check_system("expression replacer");
    bool shared = false;
    if (is_shared(e)) {
        shared = true;
        auto it = m_cache.find(e);
        if (it != m_cache.end())
            return it->second;
    }

    switch (e.kind()) {
    case expr_kind::Lit:     return save_result(e, visit_lit(e), shared);
    case expr_kind::MData:   return save_result(e, visit_mdata(e), shared);
    case expr_kind::Proj:    return save_result(e, visit_proj(e), shared);
    case expr_kind::Sort:    return save_result(e, visit_sort(e), shared);
    case expr_kind::Const:   return save_result(e, visit_constant(e), shared);
    case expr_kind::BVar:    return save_result(e, visit_var(e), shared);
    case expr_kind::MVar:    return save_result(e, visit_meta(e), shared);
    case expr_kind::FVar:    return save_result(e, visit_fvar(e), shared);
    case expr_kind::App:     return save_result(e, visit_app(e), shared);
    case expr_kind::Lambda:  return save_result(e, visit_lambda(e), shared);
    case expr_kind::Pi:      return save_result(e, visit_pi(e), shared);
    case expr_kind::Let:     return save_result(e, visit_let(e), shared);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}

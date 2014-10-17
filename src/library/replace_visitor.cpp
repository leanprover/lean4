/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include "util/interrupt.h"
#include "library/replace_visitor.h"

namespace lean {
expr replace_visitor::visit_sort(expr const & e) { lean_assert(is_sort(e)); return e; }
expr replace_visitor::visit_var(expr const & e) { lean_assert(is_var(e)); return e; }
expr replace_visitor::visit_constant(expr const & e) { lean_assert(is_constant(e)); return e; }
expr replace_visitor::visit_mlocal(expr const & e) {
    lean_assert(is_mlocal(e));
    return update_mlocal(e, visit(mlocal_type(e)));
}
expr replace_visitor::visit_meta(expr const & e) { return visit_mlocal(e); }
expr replace_visitor::visit_local(expr const & e) { return visit_mlocal(e); }
expr replace_visitor::visit_app(expr const & e) {
    lean_assert(is_app(e));
    return update_app(e, visit(app_fn(e)), visit(app_arg(e)));
}
expr replace_visitor::visit_binding(expr const & e) {
    lean_assert(is_binding(e));
    expr new_d = visit(binding_domain(e));
    expr new_b = visit(binding_body(e));
    return update_binding(e, new_d, new_b);
}
expr replace_visitor::visit_lambda(expr const & e) { return visit_binding(e); }
expr replace_visitor::visit_pi(expr const & e) { return visit_binding(e); }
expr replace_visitor::visit_macro(expr const & e) {
    lean_assert(is_macro(e));
    buffer<expr> new_args;
    for (unsigned i = 0; i < macro_num_args(e); i++)
        new_args.push_back(visit(macro_arg(e, i)));
    return update_macro(e, new_args.size(), new_args.data());
}
expr replace_visitor::save_result(expr const & e, expr && r, bool shared) {
    if (shared)
        m_cache.insert(std::make_pair(e, r));
    return r;
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
    case expr_kind::Sort:      return save_result(e, visit_sort(e), shared);
    case expr_kind::Macro:     return save_result(e, visit_macro(e), shared);
    case expr_kind::Constant:  return save_result(e, visit_constant(e), shared);
    case expr_kind::Var:       return save_result(e, visit_var(e), shared);
    case expr_kind::Meta:      return save_result(e, visit_meta(e), shared);
    case expr_kind::Local:     return save_result(e, visit_local(e), shared);
    case expr_kind::App:       return save_result(e, visit_app(e), shared);
    case expr_kind::Lambda:    return save_result(e, visit_lambda(e), shared);
    case expr_kind::Pi:        return save_result(e, visit_pi(e), shared);
    }

    lean_unreachable(); // LCOV_EXCL_LINE
}
}

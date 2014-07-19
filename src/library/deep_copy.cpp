/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/buffer.h"
#include "kernel/expr.h"
#include "kernel/replace_fn.h"

namespace lean {
expr copy(expr const & a) {
    scoped_expr_caching scope(false);
    switch (a.kind()) {
    case expr_kind::Var:      return mk_var(var_idx(a));
    case expr_kind::Constant: return mk_constant(const_name(a), const_levels(a));
    case expr_kind::Sort:     return mk_sort(sort_level(a));
    case expr_kind::Macro:    return mk_macro(to_macro(a)->m_definition, macro_num_args(a), macro_args(a));
    case expr_kind::App:      return mk_app(app_fn(a), app_arg(a));
    case expr_kind::Lambda:   return mk_lambda(binding_name(a), binding_domain(a), binding_body(a), binding_info(a));
    case expr_kind::Pi:       return mk_pi(binding_name(a), binding_domain(a), binding_body(a), binding_info(a));
    case expr_kind::Meta:     return mk_metavar(mlocal_name(a), mlocal_type(a));
    case expr_kind::Local:    return mk_local(mlocal_name(a), local_pp_name(a), mlocal_type(a), local_info(a));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr deep_copy(expr const & e) {
    scoped_expr_caching scope(false);
    return replace(e, [](expr const & e) {
            if (is_atomic(e))
                return some_expr(copy(e));
            else
                return none_expr();
        });
}
}

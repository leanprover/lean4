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
    switch (a.kind()) {
    case expr_kind::Lit:    return mk_lit(lit_value(a));
    case expr_kind::MData:  return mk_mdata(mdata_data(a), mdata_expr(a));
    case expr_kind::Proj:   return mk_proj(proj_sname(a), proj_idx(a), proj_expr(a));
    case expr_kind::BVar:   return mk_bvar(bvar_idx(a));
    case expr_kind::FVar:   return mk_local(local_name(a), local_pp_name(a), local_type(a), local_info(a));
    case expr_kind::Const:  return mk_const(const_name(a), const_levels(a));
    case expr_kind::Sort:   return mk_sort(sort_level(a));
    case expr_kind::App:    return mk_app(app_fn(a), app_arg(a));
    case expr_kind::Lambda: return mk_lambda(binding_name(a), binding_domain(a), binding_body(a), binding_info(a));
    case expr_kind::Pi:     return mk_pi(binding_name(a), binding_domain(a), binding_body(a), binding_info(a));
    case expr_kind::MVar:   return mk_mvar(mvar_name(a));
    case expr_kind::Let:    return mk_let(let_name(a), let_type(a), let_value(a), let_body(a));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr deep_copy(expr const & e) {
    return replace(e, [](expr const & e) {
            if (is_atomic(e))
                return some_expr(copy(e));
            else
                return none_expr();
        });
}
}

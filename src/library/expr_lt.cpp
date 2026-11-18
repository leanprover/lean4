/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"
#include "library/expr_lt.h"

namespace lean {
bool is_lt(expr const & a, expr const & b, bool use_hash, local_ctx const * lctx) {
    if (is_eqp(a, b))                    return false;
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    if (use_hash) {
        if (hash(a) < hash(b))           return true;
        if (hash(a) > hash(b))           return false;
    }
    if (a == b)                          return false;
    switch (a.kind()) {
    case expr_kind::Lit:
        return lit_value(a) < lit_value(b);
    case expr_kind::BVar:
        return bvar_idx(a) < bvar_idx(b);
    case expr_kind::MData:
        if (mdata_expr(a) != mdata_expr(b))
            return is_lt(mdata_expr(a), mdata_expr(b), use_hash, lctx);
        else
            return mdata_data(a) < mdata_data(b);
    case expr_kind::Proj:
        if (proj_expr(a) != proj_expr(b))
            return is_lt(proj_expr(a), proj_expr(b), use_hash, lctx);
        else if (proj_sname(a) != proj_sname(b))
            return proj_sname(a) < proj_sname(b);
        else
            return proj_idx(a) < proj_idx(b);
    case expr_kind::Const:
        if (const_name(a) != const_name(b))
            return const_name(a) < const_name(b);
        else
            return is_lt(const_levels(a), const_levels(b), use_hash);
    case expr_kind::App:
        if (app_fn(a) != app_fn(b))
            return is_lt(app_fn(a), app_fn(b), use_hash, lctx);
        else
            return is_lt(app_arg(a), app_arg(b), use_hash, lctx);
    case expr_kind::Lambda: case expr_kind::Pi:
        if (binding_domain(a) != binding_domain(b))
            return is_lt(binding_domain(a), binding_domain(b), use_hash, lctx);
        else
            return is_lt(binding_body(a), binding_body(b), use_hash, lctx);
    case expr_kind::Let:
        if (let_nondep(a) != let_nondep(b))
            return let_nondep(a) < let_nondep(b);
        else if (let_type(a) != let_type(b))
            return is_lt(let_type(a), let_type(b), use_hash, lctx);
        else if (let_value(a) != let_value(b))
            return is_lt(let_value(a), let_value(b), use_hash, lctx);
        else
            return is_lt(let_body(a), let_body(b), use_hash, lctx);
    case expr_kind::Sort:
        return is_lt(sort_level(a), sort_level(b), use_hash);
    case expr_kind::FVar:
        if (lctx) {
            if (auto d1 = lctx->find_local_decl(a))
            if (auto d2 = lctx->find_local_decl(b))
                return d1->get_idx() < d2->get_idx();
        }
        return fvar_name(a) < fvar_name(b);
    case expr_kind::MVar:
        return mvar_name(a) < mvar_name(b);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

extern "C" LEAN_EXPORT uint8 lean_expr_quick_lt(b_obj_arg a, b_obj_arg b) {
    return is_lt(expr(a, true), expr(b, true), true, nullptr);
}

extern "C" LEAN_EXPORT uint8 lean_expr_lt(b_obj_arg a, b_obj_arg b) {
    return is_lt(expr(a, true), expr(b, true), false, nullptr);
}
}

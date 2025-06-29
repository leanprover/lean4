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

bool is_lt_no_level_params(level const & a, level const & b) {
    if (is_eqp(a, b))              return false;
    if (kind(a) != kind(b)) {
        if (kind(a) == level_kind::Param || kind(b) == level_kind::Param)
            return false;
        return kind(a) < kind(b);
    }
    switch (kind(a)) {
    case level_kind::Zero:
        lean_unreachable(); // LCOV_EXCL_LINE
    case level_kind::Param:
        return false;
    case level_kind::MVar:
        return mvar_id(a) < mvar_id(b);
    case level_kind::Max:
        if (is_lt_no_level_params(max_lhs(a), max_lhs(b)))
            return true;
        else if (is_lt_no_level_params(max_lhs(b), max_lhs(a)))
            return false;
        else
            return is_lt_no_level_params(max_rhs(a), max_rhs(b));
    case level_kind::IMax:
        if (is_lt_no_level_params(imax_lhs(a), imax_lhs(b)))
            return true;
        else if (is_lt_no_level_params(imax_lhs(b), imax_lhs(a)))
            return false;
        else
            return is_lt_no_level_params(imax_rhs(a), imax_rhs(b));
    case level_kind::Succ:
        return is_lt_no_level_params(succ_of(a), succ_of(b));
    }
    lean_unreachable();
}

bool is_lt_no_level_params(levels const & as, levels const & bs) {
    if (is_nil(as))
        return !is_nil(bs);
    else if (is_nil(bs))
        return false;
    else if (is_lt_no_level_params(car(as), car(bs)))
        return true;
    else if (is_lt_no_level_params(car(bs), car(as)))
        return false;
    else
        return is_lt_no_level_params(cdr(as), cdr(bs));
}

bool is_lt_no_level_params(expr const & a, expr const & b) {
    if (is_eqp(a, b))                    return false;
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    switch (a.kind()) {
    case expr_kind::Lit:
        return lit_value(a) < lit_value(b);
    case expr_kind::BVar:
        return bvar_idx(a) < bvar_idx(b);
    case expr_kind::MData:
        if (mdata_expr(a) != mdata_expr(b))
            return is_lt_no_level_params(mdata_expr(a), mdata_expr(b));
        else
            return mdata_data(a) < mdata_data(b);
    case expr_kind::Proj:
        if (proj_expr(a) != proj_expr(b))
            return is_lt_no_level_params(proj_expr(a), proj_expr(b));
        else if (proj_sname(a) != proj_sname(b))
            return proj_sname(a) < proj_sname(b);
        else
            return proj_idx(a) < proj_idx(b);
    case expr_kind::Const:
        if (const_name(a) != const_name(b))
            return const_name(a) < const_name(b);
        else
            return is_lt_no_level_params(const_levels(a), const_levels(b));
    case expr_kind::App:
        if (is_lt_no_level_params(app_fn(a), app_fn(b)))
            return true;
        else if (is_lt_no_level_params(app_fn(b), app_fn(a)))
            return false;
        else
            return is_lt_no_level_params(app_arg(a), app_arg(b));
    case expr_kind::Lambda: case expr_kind::Pi:
        if (is_lt_no_level_params(binding_domain(a), binding_domain(b)))
            return true;
        else if (is_lt_no_level_params(binding_domain(b), binding_domain(a)))
            return false;
        else
            return is_lt_no_level_params(binding_body(a), binding_body(b));
    case expr_kind::Let:
        if (let_nondep(a) != let_nondep(b))
            return let_nondep(a) < let_nondep(b);
        else if (is_lt_no_level_params(let_type(a), let_type(b)))
            return true;
        else if (is_lt_no_level_params(let_type(b), let_type(a)))
            return false;
        else if (is_lt_no_level_params(let_value(a), let_value(b)))
            return true;
        else if (is_lt_no_level_params(let_value(b), let_value(a)))
            return false;
        else
            return is_lt_no_level_params(let_body(a), let_body(b));
    case expr_kind::Sort:
        return is_lt_no_level_params(sort_level(a), sort_level(b));
    case expr_kind::FVar:
        return fvar_name(a) < fvar_name(b);
    case expr_kind::MVar:
        return mvar_name(a) < mvar_name(b);
    }
    lean_unreachable();
}

int expr_cmp_no_level_params::operator()(expr const & e1, expr const & e2) const {
    if (is_lt_no_level_params(e1, e2))
        return -1;
    else if (is_lt_no_level_params(e2, e1))
        return 1;
    else
        return 0;
}

extern "C" LEAN_EXPORT uint8 lean_expr_quick_lt(b_obj_arg a, b_obj_arg b) {
    return is_lt(expr(a, true), expr(b, true), true, nullptr);
}

extern "C" LEAN_EXPORT uint8 lean_expr_lt(b_obj_arg a, b_obj_arg b) {
    return is_lt(expr(a, true), expr(b, true), false, nullptr);
}
}

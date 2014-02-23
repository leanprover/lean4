/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"
#include "library/expr_lt.h"

namespace lean {
bool is_lt(level const & a, level const & b, bool use_hash) {
    if (is_eqp(a, b))            return false;
    if (kind(a) != kind(b))      return kind(a) < kind(b);
    if (use_hash) {
        if (hash(a) < hash(b))   return true;
        if (hash(a) > hash(b))   return false;
    }
    if (a == b)                  return false;
    switch (kind(a)) {
    case level_kind::Zero:       return true;
    case level_kind::Succ:       return is_lt(succ_of(a), succ_of(b), use_hash);
    case level_kind::Param:      return param_id(a) < param_id(b);
    case level_kind::Meta:       return meta_id(a) < meta_id(b);
    case level_kind::Max:
        if (max_lhs(a) != max_lhs(b))
            return is_lt(max_lhs(a), max_lhs(b), use_hash);
        else
            return is_lt(max_lhs(a), max_lhs(b), use_hash);
    case level_kind::IMax:
        if (imax_lhs(a) != imax_lhs(b))
            return is_lt(imax_lhs(a), imax_lhs(b), use_hash);
        else
            return is_lt(imax_lhs(a), imax_lhs(b), use_hash);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_lt(levels const & as, levels const & bs, bool use_hash) {
    if (is_nil(as))
        return !is_nil(bs);
    if (is_nil(bs))
        return false;
    if (car(as) == car(bs))
        return is_lt(cdr(as), cdr(bs), use_hash);
    else
        return is_lt(car(as), car(bs), use_hash);
}

bool is_lt(expr const & a, expr const & b, bool use_hash) {
    if (is_eqp(a, b))                    return false;
    unsigned da = get_depth(a);
    unsigned db = get_depth(b);
    if (da < db)                         return true;
    if (da > db)                         return false;
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    if (use_hash) {
        if (a.hash() < b.hash())         return true;
        if (a.hash() > b.hash())         return false;
    }
    if (a == b)                          return false;
    switch (a.kind()) {
    case expr_kind::Var:
        return var_idx(a) < var_idx(b);
    case expr_kind::Constant:
        if (const_name(a) != const_name(b))
            return const_name(a) < const_name(b);
        else
            return is_lt(const_level_params(a), const_level_params(b), use_hash);
    case expr_kind::App:
        if (app_fn(a) != app_fn(b))
            return is_lt(app_fn(a), app_fn(b), use_hash);
        else
            return is_lt(app_arg(a), app_arg(b), use_hash);
    case expr_kind::Pair:
        if (pair_first(a) != pair_first(b))
            return is_lt(pair_first(a), pair_first(b), use_hash);
        else if (pair_second(a) != pair_second(b))
            return is_lt(pair_second(a), pair_second(b), use_hash);
        else
            return is_lt(pair_type(a), pair_type(b), use_hash);
    case expr_kind::Fst: case expr_kind::Snd:
        return is_lt(proj_arg(a), proj_arg(b), use_hash);
    case expr_kind::Sigma: case expr_kind::Lambda: case expr_kind::Pi:
        if (binder_domain(a) != binder_domain(b))
            return is_lt(binder_domain(a), binder_domain(b), use_hash);
        else
            return is_lt(binder_body(a), binder_body(b), use_hash);
    case expr_kind::Sort:
        return is_lt(sort_level(a), sort_level(b), use_hash);
    case expr_kind::Let:
        if (let_type(a) != let_type(b)) {
            return is_lt(let_type(a), let_type(b), use_hash);
        } else if (let_value(a) != let_value(b)){
            return is_lt(let_value(a), let_value(b), use_hash);
        } else {
            return is_lt(let_body(a), let_body(b), use_hash);
        }
    case expr_kind::Local: case expr_kind::Meta:
        if (mlocal_name(a) != mlocal_name(b))
            return mlocal_name(a) < mlocal_name(b);
        else
            return is_lt(mlocal_type(a), mlocal_type(b), use_hash);
    case expr_kind::Macro:
        return to_macro(a) < to_macro(b);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"
#include "library/expr_lt.h"

namespace lean {
bool is_lt(expr const & a, expr const & b, bool use_hash) {
    if (is_eqp(a, b))                    return false;
    unsigned wa = get_weight(a);
    unsigned wb = get_weight(b);
    if (wa < wb)                         return true;
    if (wa > wb)                         return false;
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
            return is_lt(const_levels(a), const_levels(b), use_hash);
    case expr_kind::App:
        if (app_fn(a) != app_fn(b))
            return is_lt(app_fn(a), app_fn(b), use_hash);
        else
            return is_lt(app_arg(a), app_arg(b), use_hash);
    case expr_kind::Lambda: case expr_kind::Pi:
        if (binding_domain(a) != binding_domain(b))
            return is_lt(binding_domain(a), binding_domain(b), use_hash);
        else
            return is_lt(binding_body(a), binding_body(b), use_hash);
    case expr_kind::Sort:
        return is_lt(sort_level(a), sort_level(b), use_hash);
    case expr_kind::Local: case expr_kind::Meta:
        if (mlocal_name(a) != mlocal_name(b))
            return mlocal_name(a) < mlocal_name(b);
        else
            return is_lt(mlocal_type(a), mlocal_type(b), use_hash);
    case expr_kind::Macro:
        if (macro_def(a) != macro_def(b))
            return macro_def(a) < macro_def(b);
        if (macro_num_args(a) != macro_num_args(b))
            return macro_num_args(a) < macro_num_args(b);
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (macro_arg(a, i) != macro_arg(b, i))
                return is_lt(macro_arg(a, i), macro_arg(b, i), use_hash);
        }
        return false;
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
    case level_kind::Global:
        return global_id(a) < global_id(b);
    case level_kind::Meta:
        return meta_id(a) < meta_id(b);
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
    unsigned wa = get_weight(a);
    unsigned wb = get_weight(b);
    if (wa < wb)                         return true;
    if (wa > wb)                         return false;
    if (a.kind() != b.kind())            return a.kind() < b.kind();
    switch (a.kind()) {
    case expr_kind::Var:
        return var_idx(a) < var_idx(b);
    case expr_kind::Constant:
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
    case expr_kind::Sort:
        return is_lt_no_level_params(sort_level(a), sort_level(b));
    case expr_kind::Local: case expr_kind::Meta:
        if (mlocal_name(a) != mlocal_name(b))
            return mlocal_name(a) < mlocal_name(b);
        else
            return is_lt_no_level_params(mlocal_type(a), mlocal_type(b));
    case expr_kind::Macro:
        if (macro_def(a) != macro_def(b))
            return macro_def(a) < macro_def(b);
        if (macro_num_args(a) != macro_num_args(b))
            return macro_num_args(a) < macro_num_args(b);
        for (unsigned i = 0; i < macro_num_args(a); i++) {
            if (is_lt_no_level_params(macro_arg(a, i), macro_arg(b, i)))
                return true;
            else if (is_lt_no_level_params(macro_arg(b, i), macro_arg(a, i)))
                return false;
        }
        return false;
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
}

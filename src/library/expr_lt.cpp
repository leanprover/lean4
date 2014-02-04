/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"

namespace lean {
bool is_lt(expr const & a, expr const & b, bool use_hash);
static bool is_lt(optional<expr> const & a, optional<expr> const & b, bool use_hash) {
    if (is_eqp(a, b))   return false;
    else if (!a && b)   return true;
    else if (a && !b)   return false;
    else return is_lt(*a, *b, use_hash);
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
    if (is_var(a))                       return var_idx(a) < var_idx(b);
    switch (a.kind()) {
    case expr_kind::Var:
        lean_unreachable(); // LCOV_EXCL_LINE
    case expr_kind::Constant:
        return const_name(a) < const_name(b);
    case expr_kind::App:
        if (num_args(a) != num_args(b))
            return num_args(a) < num_args(b);
        for (unsigned i = 0; i < num_args(a); i++) {
            if (arg(a, i) != arg(b, i))
                return is_lt(arg(a, i), arg(b, i), use_hash);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    case expr_kind::Pair:
        if (pair_first(a) != pair_first(b))
            return is_lt(pair_first(a), pair_first(b), use_hash);
        else if (pair_second(a) != pair_second(b))
            return is_lt(pair_second(a), pair_second(b), use_hash);
        else
            return is_lt(pair_type(a), pair_type(b), use_hash);
    case expr_kind::Proj:
        if (proj_first(a) != proj_first(b))
            return proj_first(a) && !proj_first(b); // first projection is smaller than the second one.
        else
            return is_lt(proj_arg(a), proj_arg(b), use_hash);
    case expr_kind::Sigma:
    case expr_kind::Lambda:
    case expr_kind::Pi: // Remark: we ignore get_abs_name because we want alpha-equivalence
        if (abst_domain(a) != abst_domain(b))
            return is_lt(abst_domain(a), abst_domain(b), use_hash);
        else
            return is_lt(abst_body(a), abst_body(b), use_hash);
    case expr_kind::Type:
        return ty_level(a) < ty_level(b);
    case expr_kind::Value:
        return to_value(a) < to_value(b);
    case expr_kind::Let:
        if (let_type(a) != let_type(b)) {
            return is_lt(let_type(a), let_type(b), use_hash);
        } else if (let_value(a) != let_value(b)){
            return is_lt(let_value(a), let_value(b), use_hash);
        } else {
            return is_lt(let_body(a), let_body(b), use_hash);
        }
    case expr_kind::MetaVar:
        if (metavar_name(a) != metavar_name(b)) {
            return metavar_name(a) < metavar_name(b);
        } else {
            auto it1  = metavar_lctx(a).begin();
            auto it2  = metavar_lctx(b).begin();
            auto end1 = metavar_lctx(a).end();
            auto end2 = metavar_lctx(b).end();
            for (; it1 != end1 && it2 != end2; ++it1, ++it2) {
                if (it1->kind() != it2->kind()) {
                    return it1->kind() < it2->kind();
                } else if (it1->s() != it2->s()) {
                    return it1->s() < it2->s();
                } else if (it1->is_inst()) {
                    if (it1->v() != it2->v())
                        return is_lt(it1->v(), it2->v(), use_hash);
                } else {
                    if (it1->n() != it2->n())
                        return it1->n() < it2->n();
                }
            }
            return it1 == end1 && it2 != end2;
        }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
}

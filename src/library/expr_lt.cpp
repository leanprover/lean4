/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"

namespace lean {
bool is_lt(expr const & a, expr const & b) {
    if (is_eqp(a, b))         return false;
    if (!a && b)              return true;  // the null expression is the smallest one
    if (a && !b)              return false;
    if (a.kind() != b.kind()) return a.kind() < b.kind();
    if (a == b)               return false;
    if (is_var(a))            return var_idx(a) < var_idx(b);
    switch (a.kind()) {
    case expr_kind::Var:
        lean_unreachable();
    case expr_kind::Constant:
        return const_name(a) < const_name(b);
    case expr_kind::App:
        if (num_args(a) != num_args(b))
            return num_args(a) < num_args(b);
        for (unsigned i = 0; i < num_args(a); i++) {
            if (arg(a, i) != arg(b, i))
                return is_lt(arg(a, i), arg(b, i));
        }
        return false;
    case expr_kind::Eq:
        if (eq_lhs(a) != eq_lhs(b))
            return is_lt(eq_lhs(a), eq_lhs(b));
        else
            return is_lt(eq_rhs(a), eq_rhs(b));
    case expr_kind::Lambda:   // Remark: we ignore get_abs_name because we want alpha-equivalence
    case expr_kind::Pi:
        if (abst_domain(a) != abst_domain(b))
            return is_lt(abst_domain(a), abst_domain(b));
        else
            return is_lt(abst_body(a), abst_body(b));
    case expr_kind::Type:
        return ty_level(a) < ty_level(b);
    case expr_kind::Value:
        return to_value(a) < to_value(b);
    case expr_kind::Let:
        if (let_type(a) != let_type(b)) {
            return is_lt(let_type(a), let_type(b));
        } else if (let_value(a) != let_value(b)){
            return is_lt(let_value(a), let_value(b));
        } else {
            return is_lt(let_body(a), let_body(b));
        }
    case expr_kind::MetaVar:
        if (metavar_idx(a) != metavar_idx(b)) {
            return metavar_idx(a) < metavar_idx(b);
        } else {
            auto it1  = metavar_ctx(a).begin();
            auto it2  = metavar_ctx(b).begin();
            auto end1 = metavar_ctx(a).end();
            auto end2 = metavar_ctx(b).end();
            for (; it1 != end1 && it2 != end2; ++it1, ++it2) {
                if (it1->kind() != it2->kind()) {
                    return it1->kind() < it2->kind();
                } else if (it1->s() != it2->s()) {
                    return it1->s() < it2->s();
                } else if (it1->is_inst()) {
                    if (it1->v() != it2->v())
                        return is_lt(it1->v(), it2->v());
                } else {
                    if (it1->n() != it2->n())
                        return it1->n() < it2->n();
                }
            }
            return false;
        }
    }
    lean_unreachable();
}
}

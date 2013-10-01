/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

namespace lean {
/** \brief Identity function for expressions. */
struct id_expr_fn {
    expr const & operator()(expr const & e) const { return e; }
};

/**
   \brief Functional object for comparing expressions.
   The parameter N is a normalization function that can be used
   to normalize sub-expressions before comparing them.
   The hashcode of expressions is used to optimize the comparison when
   parameter UseHash == true. We should set UseHash to false when N
   is not the identity function.
*/
template<typename N = id_expr_fn, bool UseHash = true>
class expr_eq_fn {
    expr_cell_pair_set m_eq_visited;
    N                  m_norm;

    bool apply(expr const & a0, expr const & b0) {
        if (is_eqp(a0, b0))                    return true;
        if (!a0 || !b0)                        return false;
        if (UseHash && a0.hash() != b0.hash()) return false;
        expr const & a = m_norm(a0);
        expr const & b = m_norm(b0);
        if (a.kind() != b.kind())            return false;
        if (is_var(a))                       return var_idx(a) == var_idx(b);
        if (is_shared(a) && is_shared(b)) {
            auto p = std::make_pair(a.raw(), b.raw());
            if (m_eq_visited.find(p) != m_eq_visited.end())
                return true;
            m_eq_visited.insert(p);
        }
        switch (a.kind()) {
        case expr_kind::Var:      lean_unreachable();
        case expr_kind::Constant: return const_name(a) == const_name(b);
        case expr_kind::App:
            if (num_args(a) != num_args(b))
                return false;
            for (unsigned i = 0; i < num_args(a); i++)
                if (!apply(arg(a, i), arg(b, i)))
                    return false;
            return true;
        case expr_kind::Eq:       return apply(eq_lhs(a), eq_lhs(b)) && apply(eq_rhs(a), eq_rhs(b));
        case expr_kind::Lambda:   // Remark: we ignore get_abs_name because we want alpha-equivalence
        case expr_kind::Pi:       return apply(abst_domain(a), abst_domain(b)) && apply(abst_body(a), abst_body(b));
        case expr_kind::Type:     return ty_level(a) == ty_level(b);
        case expr_kind::Value:    return to_value(a) == to_value(b);
        case expr_kind::Let:      return apply(let_type(a), let_type(b)) && apply(let_value(a), let_value(b)) && apply(let_body(a), let_body(b));
        case expr_kind::MetaVar:
            return metavar_idx(a) == metavar_idx(b) &&
                compare(metavar_ctx(a), metavar_ctx(b), [&](meta_entry const & e1, meta_entry const & e2) {
                        if (e1.kind() != e2.kind() || e1.s() != e2.s())
                            return false;
                        if (e1.is_inst())
                            return apply(e1.v(), e2.v());
                        else
                            return e1.n() == e2.n();
                    });
        }
        lean_unreachable();
    }
public:
    expr_eq_fn(N const & norm = N()):m_norm(norm) {
        // the return type of N()(e) should be expr const &
        static_assert(std::is_same<typename std::result_of<decltype(std::declval<N>())(expr const &)>::type,
                      expr const &>::value,
                      "The return type of CMP()(k1, k2) is not int.");
    }
    bool operator()(expr const & a, expr const & b) {
        return apply(a, b);
    }
    void clear() { m_eq_visited.clear(); }
};
}

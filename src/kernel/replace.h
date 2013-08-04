/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "buffer.h"
#include "expr.h"
#include "maps.h"
namespace lean {
/**
   \brief Functional for applying <tt>F</tt> to the subexpressions of a given expression.

   The signature of \c F is
   unsigned, expr -> expr

   F is invoked for each subexpression \c s of the input expression e.
   In a call <tt>F(n, s)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s.
*/
template<typename F>
class replace_fn {
    static_assert(std::is_same<typename std::result_of<F(expr const &, unsigned)>::type, expr>::value,
                  "replace_fn: return type of F is not expr");
    expr_cell_offset_map<expr> m_cache;
    F                          m_f;

    expr apply(expr const & e, unsigned offset) {
        bool sh = false;
        if (is_shared(e)) {
            expr_cell_offset p(e.raw(), offset);
            auto it = m_cache.find(p);
            if (it != m_cache.end())
                return it->second;
            sh = true;
        }

        expr r = m_f(e, offset);
        if (eqp(e, r)) {
            switch (e.kind()) {
            case expr_kind::Type: case expr_kind::Value: case expr_kind::Constant: case expr_kind::Var:
                break;
            case expr_kind::App:
                r = update_app(e, [=](expr const & c) { return apply(c, offset); });
                break;
            case expr_kind::Eq:
                r = update_eq(e, [=](expr const & l, expr const & r) { return std::make_pair(apply(l, offset), apply(r, offset)); });
                break;
            case expr_kind::Lambda:
            case expr_kind::Pi:
                r = update_abst(e, [=](expr const & t, expr const & b) { return std::make_pair(apply(t, offset), apply(b, offset+1)); });
                break;
            case expr_kind::Let:
                r = update_let(e, [=](expr const & v, expr const & b) { return std::make_pair(apply(v, offset), apply(b, offset+1)); });
                break;
            }
        }

        if (sh)
            m_cache.insert(std::make_pair(expr_cell_offset(e.raw(), offset), r));

        return r;
    }

public:
    replace_fn(F const & f):
        m_f(f) {
    }

    expr operator()(expr const & e) {
        return apply(e, 0);
    }
};
}

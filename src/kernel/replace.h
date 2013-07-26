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
    expr_cell_offset_map<expr> m_cache;
    F                          m_f;

    expr apply(expr const & e, unsigned offset) {
        if (is_shared(e)) {
            expr_cell_offset p(e.raw(), offset);
            auto it = m_cache.find(p);
            if (it != m_cache.end())
                return it->second;
        }

        expr r = m_f(e, offset);
        if (eqp(e, r)) {
            switch (e.kind()) {
            case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral: case expr_kind::Constant: case expr_kind::Var:
                break;
            case expr_kind::App: {
                buffer<expr> new_args;
                bool modified = false;
                for (expr const & a : args(e)) {
                    new_args.push_back(apply(a, offset));
                    if (!eqp(a, new_args.back()))
                        modified = true;
                }
                if (modified)
                    r = app(new_args.size(), new_args.data());
                else
                    r = e;
                break;
            }
            case expr_kind::Lambda:
            case expr_kind::Pi: {
                expr const & old_t = abst_type(e);
                expr const & old_b = abst_body(e);
                expr t = apply(old_t, offset);
                expr b = apply(old_b, offset+1);
                if (!eqp(t, old_t) || !eqp(b, old_b)) {
                    name const & n = abst_name(e);
                    r = is_pi(e) ? pi(n, t, b) : lambda(n, t, b);
                }
                else {
                    r = e;
                }
                break;
            }}
        }

        if (is_shared(e))
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

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include "kernel/expr.h"
#include "kernel/expr_sets.h"

namespace lean {
/**
   \brief Template for implementing expression visitors.
   The argument \c F must be a function object containing the method
   <code>
   void operator()(expr const & e, unsigned offset)
   </code>
   The \c offset is the number of binders under which \c e occurs.
*/
template<typename F>
class for_each_fn {
    std::unique_ptr<expr_cell_offset_set> m_visited;
    F                                     m_f;
    static_assert(std::is_same<typename std::result_of<F(expr const &, unsigned)>::type, bool>::value,
                  "for_each_fn: return type of m_f is not bool");

    void apply(expr const & e, unsigned offset) {
        if (is_shared(e)) {
            expr_cell_offset p(e.raw(), offset);
            if (!m_visited)
                m_visited.reset(new expr_cell_offset_set());
            if (m_visited->find(p) != m_visited->end())
                return;
            m_visited->insert(p);
        }

        if (!m_f(e, offset))
            return;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
        case expr_kind::Var: case expr_kind::MetaVar:
            return;
        case expr_kind::App:
            std::for_each(begin_args(e), end_args(e), [=](expr const & arg){ return apply(arg, offset); });
            return;
        case expr_kind::Eq:
            apply(eq_lhs(e), offset);
            apply(eq_rhs(e), offset);
            return;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            apply(abst_domain(e), offset);
            apply(abst_body(e), offset + 1);
            return;
        case expr_kind::Let:
            if (let_type(e))
                apply(let_type(e), offset);
            apply(let_value(e), offset);
            apply(let_body(e), offset + 1);
            return;
        }
    }
public:
    for_each_fn(F const & f):m_f(f) {}
    void operator()(expr const & e) { apply(e, 0); }
};
}

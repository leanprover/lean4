/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include "util/buffer.h"
#include "util/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "kernel/update_expr.h"

namespace lean {
/**
   \brief Default replace_fn postprocessor functional object. It is a
   do-nothing object.
*/
class default_replace_postprocessor {
public:
    void operator()(expr const &, expr const &) {}
};

/**
   \brief Functional for applying <tt>F</tt> to the subexpressions of a given expression.

   The signature of \c F is
   expr const &, unsigned -> expr

   F is invoked for each subexpression \c s of the input expression e.
   In a call <tt>F(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s.

   P is a "post-processing" functional object that is applied to each
   pair (old, new)
*/
class replace_fn {
    struct frame {
        expr       m_expr;
        unsigned   m_offset;
        bool       m_shared;
        unsigned   m_index;
        frame(expr const & e, unsigned o, bool s):m_expr(e), m_offset(o), m_shared(s), m_index(0) {}
    };
    typedef buffer<frame>  frame_stack;
    typedef buffer<expr>   result_stack;

    expr_cell_offset_map<expr>                      m_cache;
    std::function<expr(expr const &, unsigned)>     m_f;
    std::function<void(expr const &, expr const &)> m_post;
    frame_stack                                     m_fs;
    result_stack                                    m_rs;

    static bool is_atomic(expr const & e);
    void save_result(expr const & e, expr const & r, unsigned offset, bool shared);
    bool visit(expr const & e, unsigned offset);
    bool check_index(frame & f, unsigned idx);
    expr const & rs(int i);
    void pop_rs(unsigned num);

public:
    template<typename F, typename P = default_replace_postprocessor>
    replace_fn(F const & f, P const & p = P()):
        m_f(f), m_post(p) {}
    expr operator()(expr const & e);
    void clear();
};

template<typename F> expr replace(expr const & e, F const & f) {
    return replace_fn(f)(e);
}

template<typename F, typename P> expr replace(expr const & e, F const & f, P const & p) {
    return replace_fn(f, p)(e);
}
}

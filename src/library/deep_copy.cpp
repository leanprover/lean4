/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/buffer.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"

namespace lean {
/** \brief Implements deep copy of kernel expressions. */
class deep_copy_fn {
    expr_cell_map<expr> m_cache;

    expr apply(expr const & a) {
        bool sh = false;
        if (is_shared(a)) {
            auto r = m_cache.find(a.raw());
            if (r != m_cache.end())
                return r->second;
            sh = true;
        }
        expr r;
        switch (a.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            r = copy(a); break; // shallow copy is equivalent to deep copy for these ones.
        case expr_kind::App: {
            buffer<expr> new_args;
            for (expr const & old_arg : args(a))
                new_args.push_back(apply(old_arg));
            r = mk_app(new_args.size(), new_args.data());
            break;
        }
        case expr_kind::Eq:       r = mk_eq(apply(eq_lhs(a)), apply(eq_rhs(a))); break;
        case expr_kind::Lambda:   r = mk_lambda(abst_name(a), apply(abst_domain(a)), apply(abst_body(a))); break;
        case expr_kind::Pi:       r = mk_pi(abst_name(a), apply(abst_domain(a)), apply(abst_body(a))); break;
        case expr_kind::Let:      {
            expr new_t = let_type(a) ? apply(let_type(a)) : expr();
            r = mk_let(let_name(a), new_t, apply(let_value(a)), apply(let_body(a))); break;
        }
        }
        if (sh)
            m_cache.insert(std::make_pair(a.raw(), r));
        return r;
    }
public:
    /**
        \brief Return a new expression that is equal to the given
        argument, but does not share any memory cell with it.
    */
    expr operator()(expr const & a) { return apply(a); }
};

expr deep_copy(expr const & e) {
    return deep_copy_fn()(e);
}

}

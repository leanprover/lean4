/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "expr.h"
#include "maps.h"
#include "buffer.h"

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
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Numeral:
            r = copy(a); break; // shallow copy is equivalent to deep copy for these ones.
        case expr_kind::App: {
            buffer<expr> new_args;
            for (expr const & old_arg : args(a))
                new_args.push_back(apply(old_arg));
            r = app(new_args.size(), new_args.data());
            break;
        }
        case expr_kind::Lambda:   r = lambda(abst_name(a), apply(abst_domain(a)), apply(abst_body(a))); break;
        case expr_kind::Pi:       r = pi(abst_name(a), apply(abst_domain(a)), apply(abst_body(a))); break;
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

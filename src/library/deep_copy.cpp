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
        case expr_kind::Var:
        case expr_kind::Constant:
        case expr_kind::Sort:
        case expr_kind::Macro:   r = copy(a); break;
        case expr_kind::App:     r = mk_app(apply(app_fn(a)), apply(app_arg(a))); break;
        case expr_kind::Lambda:  r = mk_lambda(binding_name(a), apply(binding_domain(a)), apply(binding_body(a))); break;
        case expr_kind::Pi:      r = mk_pi(binding_name(a), apply(binding_domain(a)), apply(binding_body(a))); break;
        case expr_kind::Let:     r = mk_let(let_name(a), apply(let_type(a)), apply(let_value(a)), apply(let_body(a))); break;
        case expr_kind::Meta:    r = mk_metavar(mlocal_name(a), apply(mlocal_type(a))); break;
        case expr_kind::Local:   r = mk_local(mlocal_name(a), local_pp_name(a), apply(mlocal_type(a))); break;
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
expr deep_copy(expr const & e) { return deep_copy_fn()(e); }
}

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

    expr save_result(expr const & a, expr && r, bool shared) {
        if (shared)
            m_cache.insert(std::make_pair(a.raw(), r));
        return r;
    }

    optional<expr> apply(optional<expr> const & a) {
        if (a)
            return some_expr(apply(*a));
        else
            return a;
    }

    expr apply(expr const & a) {
        bool sh = false;
        if (is_shared(a)) {
            auto r = m_cache.find(a.raw());
            if (r != m_cache.end())
                return r->second;
            sh = true;
        }
        switch (a.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            return save_result(a, copy(a), sh);
        case expr_kind::App: {
            buffer<expr> new_args;
            for (expr const & old_arg : args(a))
                new_args.push_back(apply(old_arg));
            return save_result(a, mk_app(new_args), sh);
        }
        case expr_kind::Lambda:   return save_result(a, mk_lambda(abst_name(a), apply(abst_domain(a)), apply(abst_body(a))), sh);
        case expr_kind::Pi:       return save_result(a, mk_pi(abst_name(a), apply(abst_domain(a)), apply(abst_body(a))), sh);
        case expr_kind::Let:      return save_result(a, mk_let(let_name(a), apply(let_type(a)), apply(let_value(a)), apply(let_body(a))), sh);
        case expr_kind::MetaVar:
            return save_result(a,
                               update_metavar(a, [&](local_entry const & e) -> local_entry {
                                       if (e.is_inst())
                                           return mk_inst(e.s(), apply(e.v()));
                                       else
                                           return e;
                                   }),
                               sh);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
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

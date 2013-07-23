/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include <vector>
#include "expr.h"
#include "expr_functors.h"

namespace lean {

class max_sharing_functor {
    struct expr_struct_eq { unsigned operator()(expr const & e1, expr const & e2) const { return e1 == e2; }};
    typedef typename std::unordered_set<expr, expr_hash, expr_struct_eq> expr_cache;

    expr_cache m_cache;

    void cache(expr const & a) {
        a.raw()->set_max_shared();
        m_cache.insert(a);
    }

public:

    expr apply(expr const & a) {
        auto r = m_cache.find(a);
        if (r != m_cache.end()) {
            lean_assert((*r).raw()->max_shared());
            return *r;
        }
        if (a.raw()->max_shared()) {
            m_cache.insert(a);
            return a;
        }
        switch (a.kind()) {
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
            cache(a);
            return a;
        case expr_kind::App: {
            std::vector<expr> new_args;
            bool modified = false;
            for (expr const & old_arg : app_args(a)) {
                new_args.push_back(apply(old_arg));
                if (!eqp(old_arg, new_args.back()))
                    modified = true;
            }
            if (!modified) {
                cache(a);
                return a;
            }
            else {
                expr r = app(new_args.size(), new_args.data());
                cache(r);
                return r;
            }
        }
        case expr_kind::Lambda:
        case expr_kind::Pi: {
            expr const & old_t = get_abs_type(a);
            expr const & old_e = get_abs_expr(a);
            expr t = apply(old_t);
            expr e = apply(old_e);
            if (!eqp(t, old_t) || !eqp(e, old_e)) {
                name const & n     = get_abs_name(a);
                expr r = is_pi(a) ? pi(n, t, e) : lambda(n, t, e);
                cache(r);
                return r;
            }
            else {
                cache(a);
                return a;
            }
        }}
        lean_unreachable();
        return a;
    }
};

expr max_sharing(expr const & a) {
    if (a.raw()->max_shared()) {
        return a;
    }
    else {
        max_sharing_functor f;
        return f.apply(a);
    }
}

} // namespace lean

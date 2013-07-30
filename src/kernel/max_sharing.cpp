/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include "buffer.h"
#include "max_sharing.h"

namespace lean {

struct max_sharing_fn::imp {
    struct expr_struct_eq { unsigned operator()(expr const & e1, expr const & e2) const { return e1 == e2; }};
    typedef typename std::unordered_set<expr, expr_hash, expr_struct_eq> expr_cache;

    expr_cache m_cache;

    void cache(expr const & a) {
        a.raw()->set_max_shared();
        m_cache.insert(a);
    }

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
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Numeral:
            cache(a);
            return a;
        case expr_kind::App: {
            buffer<expr> new_args;
            bool modified = false;
            for (expr const & old_arg : args(a)) {
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
            expr const & old_t = abst_type(a);
            expr const & old_b = abst_body(a);
            expr t = apply(old_t);
            expr b = apply(old_b);
            if (!eqp(t, old_t) || !eqp(b, old_b)) {
                name const & n     = abst_name(a);
                expr r = is_pi(a) ? pi(n, t, b) : lambda(n, t, b);
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
    expr operator()(expr const & a) { return apply(a); }
};


max_sharing_fn::max_sharing_fn():m_imp(new imp) {}
max_sharing_fn::~max_sharing_fn() {}
expr max_sharing_fn::operator()(expr const & a) { return (*m_imp)(a); }
void max_sharing_fn::clear() { m_imp->m_cache.clear(); }

expr max_sharing(expr const & a) {
    if (a.raw()->max_shared())
        return a;
    else
        return max_sharing_fn::imp()(a);
}

} // namespace lean

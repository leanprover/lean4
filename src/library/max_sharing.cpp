/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_set>
#include "util/buffer.h"
#include "library/max_sharing.h"

namespace lean {
/**
   \brief Implementation of the functional object for creating expressions with maximally
   shared sub-expressions.
*/
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
        case expr_kind::Var: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            cache(a);
            return a;
        case expr_kind::App: {
            expr r = update_app(a, [=](expr const & c){ return apply(c); });
            cache(r);
            return r;
        }
        case expr_kind::Eq : {
            expr r = update_eq(a, [=](expr const & l, expr const & r){ return std::make_pair(apply(l), apply(r)); });
            cache(r);
            return r;
        }
        case expr_kind::Lambda:
        case expr_kind::Pi: {
            expr r = update_abst(a, [=](expr const & t, expr const & b) { return std::make_pair(apply(t), apply(b)); });
            cache(r);
            return r;
        }
        case expr_kind::Let: {
            expr r = update_let(a, [=](expr const & t, expr const & v, expr const & b) {
                    expr new_t = t ? apply(t) : expr();
                    return std::make_tuple(new_t, apply(v), apply(b));
                });
            cache(r);
            return r;
        }
        case expr_kind::MetaVar: {
            expr r = update_metavar(a, [=](meta_entry const & e) -> meta_entry {
                    if (e.is_inst())
                        return mk_inst(e.s(), apply(e.v()));
                    else
                        return e;
                });
            cache(r);
            return r;
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

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include <unordered_set>
#include <functional>
#include "util/buffer.h"
#include "util/interrupt.h"
#include "kernel/max_sharing.h"

namespace lean {
/**
   \brief Implementation of the functional object for creating expressions with maximally
   shared sub-expressions.
*/
struct max_sharing_fn::imp {
    typedef typename std::unordered_set<expr, expr_hash, std::equal_to<expr>> expr_cache;

    expr_cache m_cache;

    void cache(expr const & a) {
        a.raw()->set_max_shared();
        m_cache.insert(a);
    }

    optional<expr> apply(optional<expr> const & a) {
        if (a)
            return some_expr(apply(*a));
        else
            return a;
    }

    expr apply(expr const & a) {
        check_system("max_sharing");
        auto r = m_cache.find(a);
        if (r != m_cache.end()) {
            lean_assert((*r).raw()->max_shared());
            return *r;
        }
        if (a.raw()->max_shared()) {
            m_cache.insert(a);
            return a;
        }
        expr res;
        switch (a.kind()) {
        case expr_kind::Constant: case expr_kind::Var:
        case expr_kind::Sort:     case expr_kind::Macro:
            res = a;
            break;
        case expr_kind::Pair:
            res = update_pair(a, apply(pair_first(a)), apply(pair_second(a)), apply(pair_type(a)));
            break;
        case expr_kind::Fst:   case expr_kind::Snd:
            res = update_proj(a, apply(proj_arg(a)));
            break;
        case expr_kind::App:
            res = update_app(a, apply(app_fn(a)), apply(app_arg(a)));
            break;
        case expr_kind::Sigma: case expr_kind::Lambda: case expr_kind::Pi:
            res = update_binder(a, apply(binder_domain(a)), apply(binder_body(a)));
            break;
        case expr_kind::Let:
            res = update_let(a, apply(let_type(a)), apply(let_value(a)), apply(let_body(a)));
            break;
        case expr_kind::Meta:  case expr_kind::Local:
            res = update_mlocal(a, apply(mlocal_type(a)));
            break;
        }
        cache(res);
        return res;
    }
    expr operator()(expr const & a) { return apply(a); }
};

max_sharing_fn::max_sharing_fn():m_ptr(new imp) {}
max_sharing_fn::~max_sharing_fn() {}
expr max_sharing_fn::operator()(expr const & a) { return (*m_ptr)(a); }
void max_sharing_fn::clear() { m_ptr->m_cache.clear(); }

expr max_sharing(expr const & a) {
    if (a.raw()->max_shared())
        return a;
    else
        return max_sharing_fn::imp()(a);
}
}

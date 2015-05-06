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
#include "library/max_sharing.h"

namespace lean {
/**
   \brief Implementation of the functional object for creating expressions with maximally
   shared sub-expressions.
*/
struct max_sharing_fn::imp {
    typedef typename std::unordered_set<expr, expr_hash, is_bi_equal_proc> expr_cache;

    expr_cache m_cache;

    expr apply(expr const & a) {
        check_system("max_sharing");
        auto r = m_cache.find(a);
        if (r != m_cache.end())
            return *r;
        expr res;
        switch (a.kind()) {
        case expr_kind::Constant: case expr_kind::Var:
        case expr_kind::Sort:
            res = a;
            break;
          case expr_kind::App:
            res = update_app(a, apply(app_fn(a)), apply(app_arg(a)));
            break;
        case expr_kind::Lambda: case expr_kind::Pi:
            res = update_binding(a, apply(binding_domain(a)), apply(binding_body(a)));
            break;
        case expr_kind::Meta:  case expr_kind::Local:
            res = update_mlocal(a, apply(mlocal_type(a)));
            break;
        case expr_kind::Macro: {
            buffer<expr> new_args;
            for (unsigned i = 0; i < macro_num_args(a); i++)
                new_args.push_back(macro_arg(a, i));
            res = update_macro(a, new_args.size(), new_args.data());
            break;
        }}
        m_cache.insert(res);
        return res;
    }

    expr operator()(expr const & a) {
        // we must disable approximate/opportunistic hash-consing used in the kernel
        scoped_expr_caching disable(false);
        return apply(a);
    }

    bool already_processed(expr const & a) const {
        auto r = m_cache.find(a);
        return r != m_cache.end() && is_eqp(*r, a);
    }
};

max_sharing_fn::max_sharing_fn():m_ptr(new imp) {}
max_sharing_fn::~max_sharing_fn() {}
expr max_sharing_fn::operator()(expr const & a) { return (*m_ptr)(a); }
void max_sharing_fn::clear() { m_ptr->m_cache.clear(); }
bool max_sharing_fn::already_processed(expr const & a) const { return m_ptr->already_processed(a); }

expr max_sharing(expr const & a) {
    return max_sharing_fn::imp()(a);
}
}

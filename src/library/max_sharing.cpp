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
    typedef typename std::unordered_set<level, level_hash>                 level_cache;
    expr_cache  m_expr_cache;
    level_cache m_lvl_cache;

    level apply(level const & l) {
        auto r = m_lvl_cache.find(l);
        if (r != m_lvl_cache.end())
            return *r;
        level res;
        switch (l.kind()) {
        case level_kind::Zero:   case level_kind::Param:
        case level_kind::Global: case level_kind::Meta:
            res = l;
            break;
        case level_kind::Succ:
            res = update_succ(l, apply(succ_of(l)));
            break;
        case level_kind::Max:
            res = update_max(l, apply(max_lhs(l)), apply(max_rhs(l)));
            break;
        case level_kind::IMax:
            res = update_max(l, apply(imax_lhs(l)), apply(imax_rhs(l)));
            break;
        }
        m_lvl_cache.insert(res);
        return res;
    }

    expr apply(expr const & a) {
        check_system("max_sharing");
        auto r = m_expr_cache.find(a);
        if (r != m_expr_cache.end())
            return *r;
        expr res;
        switch (a.kind()) {
        case expr_kind::Var:
            res = a;
            break;
        case expr_kind::Constant:
            res = update_constant(a, map(const_levels(a), [&](level const & l) { return apply(l); }));
            break;
        case expr_kind::Sort:
            res = update_sort(a, apply(sort_level(a)));
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
        m_expr_cache.insert(res);
        return res;
    }

    expr operator()(expr const & a) {
        // we must disable approximate/opportunistic hash-consing used in the kernel
        scoped_expr_caching disable(false);
        return apply(a);
    }

    bool already_processed(expr const & a) const {
        auto r = m_expr_cache.find(a);
        return r != m_expr_cache.end() && is_eqp(*r, a);
    }
};

max_sharing_fn::max_sharing_fn():m_ptr(new imp) {}
max_sharing_fn::~max_sharing_fn() {}
expr max_sharing_fn::operator()(expr const & a) { return (*m_ptr)(a); }
void max_sharing_fn::clear() { m_ptr->m_expr_cache.clear(); }
bool max_sharing_fn::already_processed(expr const & a) const { return m_ptr->already_processed(a); }

expr max_sharing(expr const & a) {
    return max_sharing_fn::imp()(a);
}
}

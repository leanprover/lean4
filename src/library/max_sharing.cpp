/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <tuple>
#include <unordered_set>
#include <functional>
#include "runtime/interrupt.h"
#include "runtime/buffer.h"
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
        case level_kind::MVar:
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
        case expr_kind::BVar: case expr_kind::Lit:
        case expr_kind::MVar: case expr_kind::FVar:
            res = a;
            break;
        case expr_kind::Const:
            res = update_constant(a, map(const_levels(a), [&](level const & l) { return apply(l); }));
            break;
        case expr_kind::Sort:
            res = update_sort(a, apply(sort_level(a)));
            break;
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(a));
            res = update_mdata(a, new_e);
            break;
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(a));
            res = update_proj(a, new_e);
            break;
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(a));
            expr new_a = apply(app_arg(a));
            res = update_app(a, new_f, new_a);
            break;
        }
        case expr_kind::Lambda: case expr_kind::Pi: {
            expr new_d = apply(binding_domain(a));
            expr new_b = apply(binding_body(a));
            res = update_binding(a, new_d, new_b);
            break;
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(a));
            expr new_v = apply(let_value(a));
            expr new_b = apply(let_body(a));
            res = update_let(a, new_t, new_v, new_b);
            break;
        }
        }
        m_expr_cache.insert(res);
        return res;
    }

    expr operator()(expr const & a) {
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

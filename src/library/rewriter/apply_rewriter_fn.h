/*
Copyright (c) 2013 Microsoft Corporation.
Copyright (c) 2013 Carnegie Mellon University.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
        Soonho Kong
*/
#pragma once
#include <utility>
#include "kernel/abstract.h"
#include "kernel/context.h"
#include "kernel/environment.h"
#include "kernel/expr.h"
#include "kernel/replace.h"
#include "library/basic_thms.h"
#include "library/rewriter/rewriter.h"
#include "library/type_inferer.h"
#include "util/scoped_map.h"

namespace lean {
/**
   \brief Functional for applying <tt>F</tt> to the subexpressions of a given expression.

   The signature of \c F is
   expr const &, context const & ctx, unsigned n -> expr

   F is invoked for each subexpression \c s of the input expression e.
   In a call <tt>F(s, c, n)</tt>, \c c is the context where \c s occurs,
   and \c n is the size of \c c.

   P is a "post-processing" functional object that is applied to each
   pair (old, new)
*/
template<typename RW, typename P = default_replace_postprocessor>
class apply_rewriter_fn {
    // the return type of RW()(env, ctx, e) should be std::pair<expr, expr>
    static_assert(std::is_same<typename std::result_of<decltype(std::declval<RW>())(environment const &, context &, expr const &)>::type,
                  std::pair<expr, expr>>::value,
                  "apply_rewriter_fn: the return type of RW()(env, ctx, e) should be std::pair<expr, expr>");
    // the return type of P()(e1, e2) should be void
    static_assert(std::is_same<typename std::result_of<decltype(std::declval<P>())(expr const &, expr const &)>::type,
                  void>::value,
                  "apply_rewriter_fn: the return type of P()(e1, e2) is not void");

    typedef scoped_map<expr, std::pair<expr, expr>, expr_hash, expr_eqp> cache;
    cache                      m_cache;
    RW                         m_rw;
    P                          m_post;

    std::pair<expr, expr> apply(environment const & env, context & ctx, expr const & v) {
        bool shared = false;
        if (is_shared(v)) {
            shared = true;
            auto it = m_cache.find(v);
            if (it != m_cache.end())
                return it->second;
        }

        std::pair<expr, expr> result; // m_rw(env, ctx, v);
        // if (is_eqp(v, result.first))
        type_inferer lc(env);
        expr ty_v = lc(v, ctx);

        switch (v.kind()) {
        case expr_kind::Type:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::Value:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::Constant:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::Var:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::MetaVar:
            result = m_rw(env, ctx, v);
            break;
        case expr_kind::App: {
            buffer<std::pair<expr, expr>> results;
            for (unsigned i = 0; i < num_args(v); i++) {
                results.push_back(apply(env, ctx, arg(v, i)));
            }
            result = rewrite_app(env, ctx, v, results);
        }
            break;
        case expr_kind::Eq: {
            expr const & lhs = eq_lhs(v);
            expr const & rhs = eq_rhs(v);
            std::pair<expr, expr> result_lhs = apply(env, ctx, lhs);
            std::pair<expr, expr> result_rhs = apply(env, ctx, rhs);
            expr const & new_lhs = result_lhs.first;
            expr const & new_rhs = result_rhs.first;
            if (lhs != new_lhs) {
                if (rhs != new_rhs) {
                    // lhs & rhs changed
                    result = rewrite_eq(env, ctx, v, result_lhs, result_rhs);
                } else {
                    // only lhs changed
                    result = rewrite_eq_lhs(env, ctx, v, result_lhs);
                }
            } else {
                if (rhs != new_rhs) {
                    // only rhs changed
                    result = rewrite_eq_rhs(env, ctx, v, result_rhs);
                } else {
                    // nothing changed
                    result = std::make_pair(v, Refl(lc(v, ctx), v));
                }
            }
        }
            break;
        case expr_kind::Lambda: {
            name const & n = abst_name(v);
            expr const & ty = abst_domain(v);
            expr const & body = abst_body(v);
            context new_ctx = extend(ctx, n, ty);
            std::pair<expr, expr> result_ty   = apply(env, ctx, ty);
            std::pair<expr, expr> result_body = apply(env, new_ctx, body);
            if (ty != result_ty.first) {
                if (body != result_body.first) {
                    // ty and body changed
                    result = rewrite_lambda(env, ctx, v, result_ty, result_body);
                } else {
                    // ty changed
                    result = rewrite_lambda_type(env, ctx, v, result_ty);
                }
            } else {
                if (body != result_body.first) {
                    // body changed
                    result = rewrite_lambda_body(env, ctx, v, result_body);
                } else {
                    // nothing changed
                    result = std::make_pair(v, Refl(lc(v, ctx), v));
                }
            }
        }
            break;

        case expr_kind::Pi: {
            name const & n = abst_name(v);
            expr const & ty = abst_domain(v);
            expr const & body = abst_body(v);
            context new_ctx = extend(ctx, n, ty);
            std::pair<expr, expr> result_ty   = apply(env, ctx, ty);
            std::pair<expr, expr> result_body = apply(env, new_ctx, body);
            if (ty != result_ty.first) {
                if (body != result_body.first) {
                    // ty and body changed
                    result = rewrite_pi(env, ctx, v, result_ty, result_body);
                } else {
                    // ty changed
                    result = rewrite_pi_type(env, ctx, v, result_ty);
                }
            } else {
                if (body != result_body.first) {
                    // body changed
                    result = rewrite_pi_body(env, ctx, v, result_body);
                } else {
                    // nothing changed
                    result = std::make_pair(v, Refl(lc(v, ctx), v));
                }
            }
        }
            break;
        case expr_kind::Let: {
            name const & n    = let_name(v);
            expr const & ty   = let_type(v);
            expr const & val  = let_value(v);
            expr const & body = let_body(v);

            expr new_v = v;
            expr ty_v = lc(v, ctx);
            expr pf = Refl(ty_v, v);
            bool changed = false;

            std::pair<expr, expr> result_ty = apply(env, ctx, ty);
            if (ty != result_ty.first) {
                // ty changed
                result  = rewrite_let_type(env, ctx, new_v, result_ty);
                new_v   = result.first;
                pf      = result.second;
                changed = true;
            }

            std::pair<expr, expr> result_val = apply(env, ctx, val);
            if (val != result_val.first) {
                result = rewrite_let_value(env, ctx, new_v, result_val);
                if (changed) {
                    pf = Trans(ty_v, v, new_v, result.first, pf, result.second);
                } else {
                    pf = result.second;
                }
                new_v = result.first;
                changed = true;
            }

            context new_ctx = extend(ctx, n, ty);
            std::pair<expr, expr> result_body = apply(env, new_ctx, body);
            if (body != result_body.first) {
                result = rewrite_let_body(env, ctx, new_v, result_body);
                if (changed) {
                    pf = Trans(ty_v, v, new_v, result.first, pf, result.second);
                } else {
                    pf = result.second;
                }
                new_v = result.first;
                changed = true;
            }
            result = std::make_pair(new_v, pf);
        }
            break;
        }
        if (shared)
            m_cache.insert(std::make_pair(v, result));
        return result;
    }

public:
    apply_rewriter_fn(RW const & rw, P const & p = P()):
        m_rw(rw),
        m_post(p) {
    }
    std::pair<expr, expr> operator()(environment const & env, context & ctx, expr const & v) {
        return apply(env, ctx, v);
    }
};
}

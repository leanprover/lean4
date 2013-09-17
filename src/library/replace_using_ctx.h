/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/scoped_map.h"
#include "kernel/replace.h"

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
template<typename F, typename P = default_replace_postprocessor>
class replace_using_ctx_fn {
    static_assert(std::is_same<typename std::result_of<F(expr const &, context const &, unsigned)>::type, expr>::value,
                  "replace_using_ctx_fn: return type of F is not expr");
    typedef scoped_map<expr, expr, expr_hash, expr_eqp> cache;
    cache                      m_cache;
    F                          m_f;
    P                          m_post;

    expr apply(expr const & e, context const & ctx, unsigned offset) {
        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            auto it = m_cache.find(e);
            if (it != m_cache.end())
                return it->second;
        }

        expr r = m_f(e, ctx, offset);
        if (is_eqp(e, r)) {
            switch (e.kind()) {
            case expr_kind::Type: case expr_kind::Value: case expr_kind::Constant:
            case expr_kind::Var: case expr_kind::MetaVar:
                break;
            case expr_kind::App:
                r = update_app(e, [=](expr const & c) { return apply(c, ctx, offset); });
                break;
            case expr_kind::Eq:
                r = update_eq(e, [=](expr const & l, expr const & r) { return std::make_pair(apply(l, ctx, offset), apply(r, ctx, offset)); });
                break;
            case expr_kind::Lambda:
            case expr_kind::Pi:
                r = update_abst(e, [=](expr const & t, expr const & b) {
                        expr new_t = apply(t, ctx, offset);
                        expr new_b;
                        {
                            cache::mk_scope sc(m_cache);
                            new_b = apply(b, extend(ctx, abst_name(e), new_t), offset + 1);
                        }
                        return std::make_pair(new_t, new_b);
                    });
                break;
            case expr_kind::Let:
                r = update_let(e, [=](expr const & t, expr const & v, expr const & b) {
                        expr new_t = t ? apply(t, ctx, offset) : expr();
                        expr new_v = apply(v, ctx, offset);
                        expr new_b;
                        {
                            cache::mk_scope sc(m_cache);
                            new_b  = apply(b, extend(ctx, abst_name(e), new_t, new_v), offset+1);
                        }
                        return std::make_tuple(new_t, new_v, new_b);
                    });
                break;
            }
        }

        if (shared)
            m_cache.insert(std::make_pair(e, r));

        m_post(e, r);
        return r;
    }

public:
    replace_using_ctx_fn(F const & f, P const & p = P()):
        m_f(f),
        m_post(p) {
    }

    expr operator()(expr const & e, context const & ctx = context()) {
        return apply(e, ctx, ctx.size());
    }
};
}

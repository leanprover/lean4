/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "type_check.h"
#include "environment.h"
#include "kernel_exception.h"
#include "normalize.h"
#include "instantiate.h"
#include "scoped_map.h"
#include "builtin.h"
#include "free_vars.h"

namespace lean {
/** \brief Auxiliary functional object used to implement infer_type. */
class type_checker::imp {
    typedef scoped_map<expr, expr, expr_hash, expr_eqp> cache;

    environment     m_env;
    cache           m_cache;
    volatile bool   m_interrupted;

    expr lookup(context const & c, unsigned i) {
        auto p = lookup_ext(c, i);
        context_entry const & def = p.first;
        context const & def_c     = p.second;
        lean_assert(length(c) > length(def_c));
        return lift_free_vars(def.get_domain(), length(c) - length(def_c));
    }

    expr check_pi(expr const & e, expr const & s, context const & ctx) {
        if (is_pi(e))
            return e;
        expr r = normalize(e, m_env, ctx);
        if (is_pi(r))
            return r;
        throw function_expected_exception(m_env, ctx, s);
    }

    expr infer_pi(expr const & e, context const & ctx) {
        return check_pi(infer_type(e, ctx), e, ctx);
    }

public:
    imp(environment const & env):
        m_env(env) {
        m_interrupted = false;
    }

    level infer_universe(expr const & t, context const & ctx) {
        expr u = normalize(infer_type(t, ctx), m_env, ctx);
        if (is_type(u))
            return ty_level(u);
        if (u == Bool)
            return level();
        throw type_expected_exception(m_env, ctx, t);
    }

    expr infer_type(expr const & e, context const & ctx) {
        if (m_interrupted)
            throw interrupted();
        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            auto it = m_cache.find(e);
            if (it != m_cache.end())
                return it->second;
        }

        expr r;
        switch (e.kind()) {
        case expr_kind::Constant:
            r = m_env.get_object(const_name(e)).get_type();
            break;
        case expr_kind::Var:
            r = lookup(ctx, var_idx(e));
            break;
        case expr_kind::Type:
            r = mk_type(ty_level(e) + 1);
            break;
        case expr_kind::App: {
            expr f_t     = infer_pi(arg(e, 0), ctx);
            unsigned i   = 1;
            unsigned num = num_args(e);
            lean_assert(num >= 2);
            while (true) {
                expr const & c = arg(e, i);
                expr c_t       = infer_type(c, ctx);
                if (!is_convertible(abst_domain(f_t), c_t, m_env, ctx))
                    throw app_type_mismatch_exception(m_env, ctx, e, i, abst_domain(f_t), c_t);
                if (closed(abst_body(f_t)))
                    f_t = abst_body(f_t);
                else if (closed(c))
                    f_t = instantiate_with_closed(abst_body(f_t), c);
                else
                    f_t = instantiate(abst_body(f_t), c);
                i++;
                if (i == num) {
                    r = f_t;
                    break;
                }
                check_pi(f_t, e, ctx);
            }
            break;
        }
        case expr_kind::Eq:
            infer_type(eq_lhs(e), ctx);
            infer_type(eq_rhs(e), ctx);
            r = mk_bool_type();
            break;
        case expr_kind::Lambda: {
            infer_universe(abst_domain(e), ctx);
            expr t;
            {
                cache::mk_scope sc(m_cache);
                t = infer_type(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            }
            r = mk_pi(abst_name(e), abst_domain(e), t);
            break;
        }
        case expr_kind::Pi: {
            level l1 = infer_universe(abst_domain(e), ctx);
            level l2;
            {
                cache::mk_scope sc(m_cache);
                l2 = infer_universe(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            }
            r = mk_type(max(l1, l2));
            break;
        }
        case expr_kind::Let: {
            expr lt = infer_type(let_value(e), ctx);
            {
                cache::mk_scope sc(m_cache);
                r = infer_type(let_body(e), extend(ctx, let_name(e), lt, let_value(e)));
            }
            break;
        }
        case expr_kind::Value:
            r = to_value(e).get_type();
            break;
        }

        if (shared) {
            m_cache.insert(e, r);
        }
        return r;
    }

    void set_interrupt(bool flag) {
        m_interrupted = true;
    }

    void clear() {
        m_cache.clear();
    }
};

type_checker::type_checker(environment const & env):m_ptr(new imp(env)) {}
type_checker::~type_checker() {}
expr type_checker::infer_type(expr const & e, context const & ctx) { return m_ptr->infer_type(e, ctx); }
level type_checker::infer_universe(expr const & e, context const & ctx) { return m_ptr->infer_universe(e, ctx); }
void type_checker::clear() { m_ptr->clear(); }
void type_checker::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }

expr  infer_type(expr const & e, environment const & env, context const & ctx) {
    return type_checker(env).infer_type(e, ctx);
}

level infer_universe(expr const & t, environment const & env, context const & ctx) {
    return type_checker(env).infer_universe(t, ctx);
}
}

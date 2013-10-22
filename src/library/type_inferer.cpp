/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/flet.h"
#include "util/scoped_map.h"
#include "kernel/environment.h"
#include "kernel/normalizer.h"
#include "kernel/builtin.h"
#include "kernel/kernel_exception.h"
#include "kernel/type_checker_trace.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"
#include "kernel/metavar.h"
#include "library/reduce.h"
#include "library/type_inferer.h"

namespace lean {
static name g_x_name("x");
class type_inferer::imp {
    typedef scoped_map<expr, expr, expr_hash, expr_eqp> cache;
    typedef buffer<unification_constraint> unification_constraints;

    environment               m_env;
    context                   m_ctx;
    metavar_env *             m_menv;
    unsigned                  m_menv_timestamp;
    unification_constraints * m_uc;
    normalizer                m_normalizer;
    cache                     m_cache;
    volatile bool             m_interrupted;

    expr normalize(expr const & e, context const & ctx) {
        return m_normalizer(e, ctx, m_menv);
    }

    expr check_type(expr const & e, expr const & s, context const & ctx) {
        if (is_type(e))
            return e;
        if (e == Bool)
            return Type();
        expr u = normalize(e, ctx);
        if (is_type(u))
            return u;
        if (u == Bool)
            return Type();
        if (has_metavar(u) && m_menv) {
            trace tr = mk_type_expected_trace(ctx, s);
            m_uc->push_back(mk_convertible_constraint(ctx, u, TypeU, tr));
            return u;
        }
        throw type_expected_exception(m_env, ctx, s);
    }

    expr get_range(expr t, expr const & e, context const & ctx) {
        unsigned num = num_args(e) - 1;
        while (num > 0) {
            --num;
            if (is_pi(t)) {
                t = abst_body(t);
            } else {
                t = m_normalizer(t, ctx);
                if (is_pi(t)) {
                    t = abst_body(t);
                } else if (has_metavar(t) && m_menv) {
                    // Create two fresh variables A and B,
                    // and assign r == (Pi(x : A), B x)
                    expr A   = m_menv->mk_metavar(ctx);
                    expr B   = m_menv->mk_metavar(ctx);
                    expr p   = mk_pi(g_x_name, A, B(Var(0)));
                    trace tr = mk_function_expected_trace(ctx, e);
                    m_uc->push_back(mk_eq_constraint(ctx, t, p, tr));
                    t        = abst_body(p);
                } else {
                    throw function_expected_exception(m_env, ctx, e);
                }
            }
        }
        if (closed(t))
            return t;
        else
            return instantiate(t, num_args(e)-1, &arg(e, 1));
    }

    void set_menv(metavar_env * menv) {
        if (m_menv == menv) {
            // Check whether m_menv has been updated since the last time the checker has been invoked
            if (m_menv && m_menv->get_timestamp() > m_menv_timestamp) {
                m_menv_timestamp = m_menv->get_timestamp();
                m_cache.clear();
            }
        } else {
            m_menv = menv;
            m_cache.clear();
            m_menv_timestamp = m_menv ? m_menv->get_timestamp() : 0;
        }
    }

    expr infer_type(expr const & e, context const & ctx) {
        // cheap cases, we do not cache results
        switch (e.kind()) {
        case expr_kind::MetaVar:
            if (m_menv) {
                if (m_menv->is_assigned(e))
                    return infer_type(m_menv->get_subst(e), ctx);
                else
                    return m_menv->get_type(e);
            } else {
                throw kernel_exception(m_env, "unexpected metavariable occurrence");
            }
        case expr_kind::Constant: {
            object const & obj = m_env.get_object(const_name(e));
            if (obj.has_type())
                return obj.get_type();
            else
                throw exception("type incorrect expression");
            break;
        }
        case expr_kind::Var: {
            auto p = lookup_ext(ctx, var_idx(e));
            context_entry const & ce = p.first;
            if (ce.get_domain()) {
                context const & ce_ctx   = p.second;
                return lift_free_vars(ce.get_domain(), ctx.size() - ce_ctx.size());
            }
            // Remark: the case where ce.get_domain() is not
            // available is not considered cheap.
            break;
        }
        case expr_kind::Eq:
            return mk_bool_type();
        case expr_kind::Value:
            return to_value(e).get_type();
        case expr_kind::Type:
            return mk_type(ty_level(e) + 1);
        case expr_kind::App: case expr_kind::Lambda:
        case expr_kind::Pi:  case expr_kind::Let:
            break; // expensive cases
        }

        check_interrupted(m_interrupted);
        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            auto it = m_cache.find(e);
            if (it != m_cache.end())
                return it->second;
        }

        expr r;
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Eq:
        case expr_kind::Value:    case expr_kind::Type:
        case expr_kind::MetaVar:
            lean_unreachable();
        case expr_kind::Var: {
            auto p = lookup_ext(ctx, var_idx(e));
            context_entry const & ce = p.first;
            context const & ce_ctx   = p.second;
            lean_assert(!ce.get_domain());
            r = lift_free_vars(infer_type(ce.get_body(), ce_ctx), ctx.size() - ce_ctx.size());
            break;
        }
        case expr_kind::App: {
            expr const & f = arg(e, 0);
            expr f_t = infer_type(f, ctx);
            r = get_range(f_t, e, ctx);
            break;
        }
        case expr_kind::Lambda: {
            cache::mk_scope sc(m_cache);
            r = mk_pi(abst_name(e), abst_domain(e), infer_type(abst_body(e), extend(ctx, abst_name(e), abst_domain(e))));
            break;
        }
        case expr_kind::Pi: {
            expr t1  = check_type(infer_type(abst_domain(e), ctx), abst_domain(e), ctx);
            expr t2;
            {
                cache::mk_scope sc(m_cache);
                context new_ctx = extend(ctx, abst_name(e), abst_domain(e));
                t2 = check_type(infer_type(abst_body(e), new_ctx), abst_body(e), new_ctx);
            }
            if (is_type(t1) && is_type(t2)) {
                r = mk_type(max(ty_level(t1), ty_level(t2)));
            } else {
                lean_assert(m_uc);
                trace tr = mk_max_type_trace(ctx, e);
                r = m_menv->mk_metavar(ctx);
                m_uc->push_back(mk_max_constraint(ctx, t1, t2, r, tr));
            }
            break;
        }
        case expr_kind::Let: {
            cache::mk_scope sc(m_cache);
            r = infer_type(let_body(e), extend(ctx, let_name(e), let_type(e), let_value(e)));
            break;
        }}

        if (shared) {
            m_cache.insert(e, r);
        }
        return r;
    }

    void set_ctx(context const & ctx) {
        if (!is_eqp(m_ctx, ctx)) {
            clear();
            m_ctx = ctx;
        }
    }

public:
    imp(environment const & env):
        m_env(env),
        m_normalizer(env) {
        m_interrupted    = false;
        m_menv           = nullptr;
        m_menv_timestamp = 0;
        m_uc             = nullptr;
    }

    expr operator()(expr const & e, context const & ctx, metavar_env * menv, buffer<unification_constraint> & uc) {
        set_ctx(ctx);
        set_menv(menv);
        flet<unification_constraints*> set(m_uc, &uc);
        return infer_type(e, ctx);
    }

    void set_interrupt(bool flag) {
        m_interrupted = flag;
        m_normalizer.set_interrupt(flag);
    }

    void clear() {
        m_cache.clear();
        m_normalizer.clear();
        m_ctx            = context();
        m_menv           = nullptr;
        m_menv_timestamp = 0;
    }
};
type_inferer::type_inferer(environment const & env):m_ptr(new imp(env)) {}
type_inferer::~type_inferer() {}
expr type_inferer::operator()(expr const & e, context const & ctx, metavar_env * menv, buffer<unification_constraint> & uc) {
    return m_ptr->operator()(e, ctx, menv, uc);
}
expr type_inferer::operator()(expr const & e, context const & ctx) {
    buffer<unification_constraint> uc;
    return operator()(e, ctx, nullptr, uc);
}
void type_inferer::clear() { m_ptr->clear(); }
void type_inferer::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
}

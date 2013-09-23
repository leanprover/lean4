/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/scoped_map.h"
#include "util/flet.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/normalizer.h"
#include "kernel/instantiate.h"
#include "kernel/builtin.h"
#include "kernel/free_vars.h"
#include "kernel/metavar.h"

namespace lean {
static name g_x_name("x");
/** \brief Auxiliary functional object used to implement infer_type. */
class type_checker::imp {
    typedef scoped_map<expr, expr, expr_hash, expr_eqp> cache;

    environment const &    m_env;
    cache                  m_cache;
    normalizer             m_normalizer;
    metavar_env *          m_menv;
    unsigned               m_menv_timestamp;
    unification_problems * m_up;
    volatile bool          m_interrupted;

    expr lookup(context const & c, unsigned i) {
        auto p = lookup_ext(c, i);
        context_entry const & def = p.first;
        context const & def_c     = p.second;
        lean_assert(c.size() > def_c.size());
        return lift_free_vars(def.get_domain(), c.size() - def_c.size());
    }

    expr check_pi(expr const & e, expr const & s, context const & ctx) {
        if (is_pi(e))
            return e;
        expr r = m_normalizer(e, ctx);
        if (is_pi(r))
            return r;
        if (has_metavar(r) && m_menv && m_up) {
            // Create two fresh variables A and B,
            // and assign r == (Pi(x : A), B x)
            expr A = m_menv->mk_metavar(ctx);
            expr B = m_menv->mk_metavar(ctx);
            expr p = mk_pi(g_x_name, A, B(Var(0)));
            if (is_metavar(r) && !has_meta_context(r)) {
                // cheap case
                m_menv->assign(r, p);
            } else {
                m_up->add_eq(ctx, r, p);
            }
            return p;
        }
        throw function_expected_exception(m_env, ctx, s);
    }

    level infer_universe_core(expr const & t, context const & ctx) {
        expr u = m_normalizer(infer_type_core(t, ctx), ctx);
        if (is_type(u))
            return ty_level(u);
        if (u == Bool)
            return level();
        if (has_metavar(u) && m_menv && m_up) {
            // Remark: in the current implementation we don't have level constraints and variables
            // in the unification problem set. So, we assume the metavariable is in level 0.
            // This is a crude approximation that works most of the time.
            // A better solution is consists in creating a fresh universe level k and
            // associate the constraint that u == Type k.
            // Later the constraint must be solved in the elaborator.
            if (is_metavar(u) && !has_meta_context(u)) {
                // cheap case
                m_menv->assign(u, Type());
            } else {
                m_up->add_eq(ctx, u, Type());
            }
            return level();
        }
        throw type_expected_exception(m_env, ctx, t);
    }

    expr infer_type_core(expr const & e, context const & ctx) {
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
        case expr_kind::MetaVar:
            if (m_menv && m_up) {
                return m_menv->get_type(e, *m_up);
            } else {
                throw kernel_exception(m_env, "unexpected metavariable occurrence");
            }
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
            unsigned num = num_args(e);
            lean_assert(num >= 2);
            buffer<expr> arg_types;
            for (unsigned i = 0; i < num; i++) {
                arg_types.push_back(infer_type_core(arg(e, i), ctx));
            }
            expr f_t     = check_pi(arg_types[0], e, ctx);
            unsigned i   = 1;
            while (true) {
                expr const & c   = arg(e, i);
                expr const & c_t = arg_types[i];
                if (!is_convertible_core(c_t, abst_domain(f_t), ctx))
                    throw app_type_mismatch_exception(m_env, ctx, e, arg_types.size(), arg_types.data());
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
                f_t = check_pi(f_t, e, ctx);
            }
            break;
        }
        case expr_kind::Eq:
            infer_type_core(eq_lhs(e), ctx);
            infer_type_core(eq_rhs(e), ctx);
            r = mk_bool_type();
            break;
        case expr_kind::Lambda: {
            infer_universe_core(abst_domain(e), ctx);
            expr t;
            {
                cache::mk_scope sc(m_cache);
                t = infer_type_core(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            }
            r = mk_pi(abst_name(e), abst_domain(e), t);
            break;
        }
        case expr_kind::Pi: {
            level l1 = infer_universe_core(abst_domain(e), ctx);
            level l2;
            {
                cache::mk_scope sc(m_cache);
                l2 = infer_universe_core(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            }
            r = mk_type(max(l1, l2));
            break;
        }
        case expr_kind::Let: {
            expr lt = infer_type_core(let_value(e), ctx);
            if (let_type(e)) {
                infer_universe_core(let_type(e), ctx); // check if it is really a type
                if (!is_convertible_core(lt, let_type(e), ctx))
                    throw def_type_mismatch_exception(m_env, ctx, let_name(e), let_type(e), let_value(e), lt);
            }
            {
                cache::mk_scope sc(m_cache);
                expr t = infer_type_core(let_body(e), extend(ctx, let_name(e), lt, let_value(e)));
                r = instantiate(t, let_value(e));
            }
            break;
        }
        case expr_kind::Value: {
            // Check if the builtin value (or its set) is declared in the environment.
            name const & n = to_value(e).get_name();
            object const & obj = m_env.get_object(n);
            if (obj && ((obj.is_builtin() && obj.get_value() == e) || (obj.is_builtin_set() && obj.in_builtin_set(e)))) {
                r = to_value(e).get_type();
            } else {
                throw invalid_builtin_value_reference(m_env, e);
            }
            break;
        }
        }

        if (shared) {
            m_cache.insert(e, r);
        }
        return r;
    }

    bool is_convertible_core(expr const & t1, expr const & t2, context const & ctx) {
        return m_normalizer.is_convertible(t1, t2, ctx, m_menv, m_up);
    }

    void set_menv(metavar_env * menv) {
        if (m_menv == menv) {
            // Check whether m_menv has been updated since the last time the normalizer has been invoked
            if (m_menv && m_menv->get_timestamp() > m_menv_timestamp) {
                clear();
                m_menv_timestamp = m_menv->get_timestamp();
            }
        } else {
            clear();
            m_menv = menv;
            m_menv_timestamp = m_menv ? m_menv->get_timestamp() : 0;
        }
    }

public:
    imp(environment const & env):
        m_env(env),
        m_normalizer(env) {
        m_menv           = nullptr;
        m_menv_timestamp = 0;
        m_up             = nullptr;
        m_interrupted    = false;
    }

    level infer_universe(expr const & t, context const & ctx, metavar_env * menv, unification_problems * up) {
        set_menv(menv);
        flet<unification_problems*> set(m_up, up);
        return infer_universe_core(t, ctx);
    }

    expr infer_type(expr const & e, context const & ctx, metavar_env * menv, unification_problems * up) {
        set_menv(menv);
        flet<unification_problems*> set(m_up, up);
        return infer_type_core(e, ctx);
    }

    bool is_convertible(expr const & t1, expr const & t2, context const & ctx, metavar_env * menv, unification_problems * up) {
        set_menv(menv);
        flet<unification_problems*> set(m_up, up);
        return is_convertible_core(t1, t2, ctx);
    }

    void set_interrupt(bool flag) {
        m_interrupted = flag;
        m_normalizer.set_interrupt(flag);
    }

    void clear() {
        m_cache.clear();
        m_normalizer.clear();
        m_menv           = nullptr;
        m_menv_timestamp = 0;
    }

    normalizer & get_normalizer() {
        return m_normalizer;
    }
};

type_checker::type_checker(environment const & env):m_ptr(new imp(env)) {}
type_checker::~type_checker() {}
expr type_checker::infer_type(expr const & e, context const & ctx, metavar_env * menv, unification_problems * up) {
    return m_ptr->infer_type(e, ctx, menv, up);
}
level type_checker::infer_universe(expr const & e, context const & ctx, metavar_env * menv, unification_problems * up) {
    return m_ptr->infer_universe(e, ctx, menv, up);
}
void type_checker::clear() { m_ptr->clear(); }
void type_checker::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
bool type_checker::is_convertible(expr const & t1, expr const & t2, context const & ctx, metavar_env * menv, unification_problems * up) {
    return m_ptr->is_convertible(t1, t2, ctx, menv, up);
}
normalizer & type_checker::get_normalizer() { return m_ptr->get_normalizer(); }

expr  infer_type(expr const & e, environment const & env, context const & ctx) {
    return type_checker(env).infer_type(e, ctx);
}
}

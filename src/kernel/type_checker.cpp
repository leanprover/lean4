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
#include "kernel/type_checker_trace.h"

namespace lean {
static name g_x_name("x");
/** \brief Auxiliary functional object used to implement infer_type. */
class type_checker::imp {
    typedef scoped_map<expr, expr, expr_hash, expr_eqp> cache;
    typedef buffer<unification_constraint> unification_constraints;

    environment const &       m_env;
    cache                     m_cache;
    normalizer                m_normalizer;
    context                   m_ctx;
    metavar_env *             m_menv;
    unsigned                  m_menv_timestamp;
    unification_constraints * m_uc;
    volatile bool             m_interrupted;

    expr normalize(expr const & e, context const & ctx) {
        return m_normalizer(e, ctx, m_menv);
    }

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
        expr r = normalize(e, ctx);
        if (is_pi(r))
            return r;
        if (has_metavar(r) && m_menv) {
            // Create two fresh variables A and B,
            // and assign r == (Pi(x : A), B x)
            expr A   = m_menv->mk_metavar(ctx);
            expr B   = m_menv->mk_metavar(ctx);
            expr p   = mk_pi(g_x_name, A, B(Var(0)));
            trace tr = mk_function_expected_trace(ctx, s);
            m_uc->push_back(mk_eq_constraint(ctx, r, p, tr));
            return p;
        }
        throw function_expected_exception(m_env, ctx, s);
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
            if (m_menv) {
                if (m_menv->is_assigned(e))
                    return infer_type_core(m_menv->get_subst(e), ctx);
                else
                    return m_menv->get_type(e);
            } else {
                throw kernel_exception(m_env, "unexpected metavariable occurrence");
            }
            break;
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
                auto mk_trace = [&](){ return mk_app_type_match_trace(ctx, e, i); }; // thunk for creating trace object if needed
                if (!is_convertible(c_t, abst_domain(f_t), ctx, mk_trace))
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
            expr d = infer_type_core(abst_domain(e), ctx);
            check_type(d, abst_domain(e), ctx);
            expr t;
            {
                cache::mk_scope sc(m_cache);
                t = infer_type_core(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            }
            r = mk_pi(abst_name(e), abst_domain(e), t);
            break;
        }
        case expr_kind::Pi: {
            expr t1  = check_type(infer_type_core(abst_domain(e), ctx), abst_domain(e), ctx);
            expr t2;
            {
                cache::mk_scope sc(m_cache);
                context new_ctx = extend(ctx, abst_name(e), abst_domain(e));
                t2 = check_type(infer_type_core(abst_body(e), new_ctx), abst_body(e), new_ctx);
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
            expr lt = infer_type_core(let_value(e), ctx);
            if (let_type(e)) {
                expr ty = infer_type_core(let_type(e), ctx);
                check_type(ty, let_type(e), ctx); // check if it is really a type
                auto mk_trace = [&](){ return mk_def_type_match_trace(ctx, let_name(e), let_value(e)); }; // thunk for creating trace object if needed
                if (!is_convertible(lt, let_type(e), ctx, mk_trace))
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

    bool is_convertible_core(expr const & given, expr const & expected) {
        if (given == expected) {
            return true;
        } else {
            expr const * g = &given;
            expr const * e = &expected;
            while (true) {
                if (is_type(*e) && is_type(*g)) {
                    if (m_env.is_ge(ty_level(*e), ty_level(*g)))
                        return true;
                }

                if (is_type(*e) && *g == mk_bool_type())
                    return true;

                if (is_pi(*e) && is_pi(*g) && abst_domain(*e) == abst_domain(*g)) {
                    g = &abst_body(*g);
                    e = &abst_body(*e);
                } else {
                    return false;
                }
            }
        }
    }

    template<typename MkTrace>
    bool is_convertible(expr const & given, expr const & expected, context const & ctx, MkTrace const & mk_trace) {
        if (is_convertible_core(given, expected))
            return true;
        expr new_given    = normalize(given, ctx);
        expr new_expected = normalize(expected, ctx);
        if (is_convertible_core(new_given, new_expected))
            return true;
        if (m_menv && (has_metavar(new_given) || has_metavar(new_expected))) {
            m_uc->push_back(mk_convertible_constraint(ctx, new_given, new_expected, mk_trace()));
            return true;
        }
        return false;
    }


    void set_ctx(context const & ctx) {
        if (!is_eqp(m_ctx, ctx)) {
            clear();
            m_ctx = ctx;
        }
    }

    void set_menv(metavar_env * menv) {
        if (m_menv == menv) {
            // Check whether m_menv has been updated since the last time the type checker has been invoked
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
        m_uc              = nullptr;
        m_interrupted     = false;
    }

    expr infer_type(expr const & e, context const & ctx, metavar_env * menv, buffer<unification_constraint> & uc) {
        set_ctx(ctx);
        set_menv(menv);
        flet<unification_constraints*> set_uc(m_uc, &uc);
        return infer_type_core(e, ctx);
    }

    bool is_convertible(expr const & t1, expr const & t2, context const & ctx) {
        set_ctx(ctx);
        set_menv(nullptr);
        auto mk_trace = [](){ lean_unreachable(); return trace(); };
        return is_convertible(t1, t2, ctx, mk_trace);
    }

    void check_type(expr const & e, context const & ctx) {
        set_ctx(ctx);
        set_menv(nullptr);
        expr t = infer_type_core(e, ctx);
        check_type(t, e, ctx);
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

    normalizer & get_normalizer() {
        return m_normalizer;
    }
};

type_checker::type_checker(environment const & env):m_ptr(new imp(env)) {}
type_checker::~type_checker() {}
expr type_checker::infer_type(expr const & e, context const & ctx, metavar_env * menv, buffer<unification_constraint> & uc) {
    return m_ptr->infer_type(e, ctx, menv, uc);
}
expr type_checker::infer_type(expr const & e, context const & ctx) {
    buffer<unification_constraint> uc;
    return infer_type(e, ctx, nullptr, uc);
}
bool type_checker::is_convertible(expr const & t1, expr const & t2, context const & ctx) {
    return m_ptr->is_convertible(t1, t2, ctx);
}
void type_checker::check_type(expr const & e, context const & ctx) {
    m_ptr->check_type(e, ctx);
}
void type_checker::clear() { m_ptr->clear(); }
void type_checker::set_interrupt(bool flag) { m_ptr->set_interrupt(flag); }
normalizer & type_checker::get_normalizer() { return m_ptr->get_normalizer(); }

expr  infer_type(expr const & e, environment const & env, context const & ctx) {
    return type_checker(env).infer_type(e, ctx);
}
bool is_convertible(expr const & given, expr const & expected, environment const & env, context const & ctx) {
    return type_checker(env).is_convertible(given, expected, ctx);
}
}

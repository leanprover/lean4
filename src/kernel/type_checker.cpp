/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/scoped_map.h"
#include "util/flet.h"
#include "util/interrupt.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/normalizer.h"
#include "kernel/instantiate.h"
#include "kernel/builtin.h"
#include "kernel/free_vars.h"
#include "kernel/type_checker_justification.h"

namespace lean {
static name g_x_name("x");
/** \brief Auxiliary functional object used to implement infer_type. */
class type_checker::imp {
    typedef scoped_map<expr, expr, expr_hash_alloc, expr_eqp> cache;
    typedef buffer<unification_constraint> unification_constraints;

    ro_environment::weak_ref  m_env;
    cache                     m_cache;
    normalizer                m_normalizer;
    context                   m_ctx;
    cached_metavar_env        m_menv;
    unification_constraints * m_uc;

    ro_environment env() const {
        return ro_environment(m_env);
    }

    expr normalize(expr const & e, context const & ctx) {
        return m_normalizer(e, ctx);
    }

    expr check_pi(expr const & e, expr const & s, context const & ctx) {
        if (is_pi(e))
            return e;
        expr r = normalize(e, ctx);
        if (is_pi(r))
            return r;
        if (has_metavar(r) && m_menv && m_uc) {
            // Create two fresh variables A and B,
            // and assign r == (Pi(x : A), B x)
            expr A   = m_menv->mk_metavar(ctx);
            expr B   = m_menv->mk_metavar(ctx);
            expr p   = mk_pi(g_x_name, A, B(Var(0)));
            justification jst = mk_function_expected_justification(ctx, s);
            m_uc->push_back(mk_eq_constraint(ctx, r, p, jst));
            return p;
        }
        throw function_expected_exception(env(), ctx, s);
    }

    expr check_type(expr const & e, expr const & s, context const & ctx) {
        if (is_type(e))
            return e;
        if (is_bool(e))
            return Type();
        expr u = normalize(e, ctx);
        if (is_type(u))
            return u;
        if (is_bool(u))
            return Type();
        if (has_metavar(u) && m_menv && m_uc) {
            justification jst = mk_type_expected_justification(ctx, s);
            m_uc->push_back(mk_convertible_constraint(ctx, u, TypeU, jst));
            return u;
        }
        throw type_expected_exception(env(), ctx, s);
    }

    expr save_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache.insert(e, r);
        return r;
    }

    expr infer_type_core(expr const & e, context const & ctx) {
        check_system("type checker");
        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            auto it = m_cache.find(e);
            if (it != m_cache.end())
                return it->second;
        }

        switch (e.kind()) {
        case expr_kind::MetaVar:
            if (m_menv) {
                if (m_menv->is_assigned(e)) {
                    optional<expr> s = m_menv->get_subst(e);
                    lean_assert(s);
                    return infer_type_core(*s, ctx);
                } else {
                    return m_menv->get_type(e);
                }
            } else {
                throw unexpected_metavar_occurrence(env(), e);
            }
        case expr_kind::Constant: {
            if (const_type(e)) {
                return save_result(e, *const_type(e), shared);
            } else {
                object const & obj = env()->get_object(const_name(e));
                if (obj.has_type())
                    return save_result(e, obj.get_type(), shared);
                else
                    throw has_no_type_exception(env(), e);
            }
        }
        case expr_kind::Var: {
            unsigned i = var_idx(e);
            auto p = lookup_ext(ctx, i);
            context_entry const & def = p.first;
            context const & def_ctx   = p.second;
            lean_assert(ctx.size() > def_ctx.size());
            if (optional<expr> const & d = def.get_domain()) {
                return save_result(e, lift_free_vars(*d, ctx.size() - def_ctx.size()), shared);
            } else {
                optional<expr> const & b = def.get_body();
                lean_assert(b);
                expr t = infer_type_core(*b, def_ctx);
                return save_result(e, lift_free_vars(t, ctx.size() - def_ctx.size()), shared);
            }
        }
        case expr_kind::Type:
            return save_result(e, mk_type(ty_level(e) + 1), shared);
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
                auto mk_justification = [&](){ return mk_app_type_match_justification(ctx, e, i); }; // thunk for creating justification object if needed
                if (!is_convertible(c_t, abst_domain(f_t), ctx, mk_justification))
                    throw app_type_mismatch_exception(env(), ctx, e, arg_types.size(), arg_types.data());
                if (closed(abst_body(f_t)))
                    f_t = abst_body(f_t);
                else if (closed(c))
                    f_t = instantiate_with_closed(abst_body(f_t), c); // TODO(Leo): m_menv.to_some_menv());
                else
                    f_t = instantiate(abst_body(f_t), c); // TODO(Leo): m_menv.to_some_menv());
                i++;
                if (i == num)
                    return save_result(e, f_t, shared);
                f_t = check_pi(f_t, e, ctx);
            }
        }
        case expr_kind::Eq:
            infer_type_core(eq_lhs(e), ctx);
            infer_type_core(eq_rhs(e), ctx);
            return save_result(e, mk_bool_type(), shared);
        case expr_kind::Lambda: {
            expr d = infer_type_core(abst_domain(e), ctx);
            check_type(d, abst_domain(e), ctx);
            {
                cache::mk_scope sc(m_cache);
                return save_result(e,
                                   mk_pi(abst_name(e), abst_domain(e), infer_type_core(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)))),
                                   shared);
            }
        }
        case expr_kind::Pi: {
            expr t1  = check_type(infer_type_core(abst_domain(e), ctx), abst_domain(e), ctx);
            optional<expr> t2;
            context new_ctx = extend(ctx, abst_name(e), abst_domain(e));
            {
                cache::mk_scope sc(m_cache);
                t2 = check_type(infer_type_core(abst_body(e), new_ctx), abst_body(e), new_ctx);
            }
            if (is_type(t1) && is_type(*t2)) {
                return save_result(e, mk_type(max(ty_level(t1), ty_level(*t2))), shared);
            } else {
                lean_assert(m_uc);
                justification jst = mk_max_type_justification(ctx, e);
                expr r = m_menv->mk_metavar(ctx);
                m_uc->push_back(mk_max_constraint(new_ctx, lift_free_vars(t1, 0, 1), *t2, r, jst));
                return save_result(e, r, shared);
            }
        }
        case expr_kind::Let: {
            expr lt = infer_type_core(let_value(e), ctx);
            if (let_type(e)) {
                expr ty = infer_type_core(*let_type(e), ctx);
                check_type(ty, *let_type(e), ctx); // check if it is really a type
                // thunk for creating justification object if needed
                auto mk_justification = [&](){ return mk_def_type_match_justification(ctx, let_name(e), let_value(e)); };
                if (!is_convertible(lt, *let_type(e), ctx, mk_justification))
                    throw def_type_mismatch_exception(env(), ctx, let_name(e), *let_type(e), let_value(e), lt);
            }
            {
                cache::mk_scope sc(m_cache);
                expr t = infer_type_core(let_body(e), extend(ctx, let_name(e), lt, let_value(e)));
                return save_result(e,
                                   instantiate(t, let_value(e)), // TODO(Leo): m_menv.to_some_menv()),
                                   shared);
            }
        }
        case expr_kind::Value: {
            // Check if the builtin value (or its set) is declared in the environment.
            name const & n = to_value(e).get_name();
            object obj = env()->get_object(n);
            if ((obj.is_builtin() && obj.get_value() == e) || (obj.is_builtin_set() && obj.in_builtin_set(e))) {
                return save_result(e, to_value(e).get_type(), shared);
            } else {
                throw invalid_builtin_value_reference(env(), e);
            }
        }
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }

    bool is_convertible_core(expr const & given, expr const & expected) {
        if (given == expected) {
            return true;
        } else {
            expr const * g = &given;
            expr const * e = &expected;
            while (true) {
                if (is_type(*e) && is_type(*g)) {
                    if (env()->is_ge(ty_level(*e), ty_level(*g)))
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

    template<typename MkJustification>
    bool is_convertible(expr const & given, expr const & expected, context const & ctx, MkJustification const & mk_justification) {
        if (is_convertible_core(given, expected))
            return true;
        expr new_given    = normalize(given, ctx);
        expr new_expected = normalize(expected, ctx);
        if (is_convertible_core(new_given, new_expected))
            return true;
        if (m_menv && m_uc && (has_metavar(new_given) || has_metavar(new_expected))) {
            m_uc->push_back(mk_convertible_constraint(ctx, given, expected, mk_justification()));
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

    void update_menv(optional<metavar_env> const & menv) {
        if (m_menv.update(menv))
            clear_cache();
    }

public:
    imp(ro_environment const & env):
        m_env(env),
        m_normalizer(env) {
        m_uc              = nullptr;
    }

    expr infer_type(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * uc) {
        set_ctx(ctx);
        update_menv(menv);
        flet<unification_constraints*> set_uc(m_uc, uc);
        return infer_type_core(e, ctx);
    }

    bool is_convertible(expr const & t1, expr const & t2, context const & ctx) {
        set_ctx(ctx);
        update_menv(none_menv());
        auto mk_justification = [](){
            lean_unreachable(); return justification(); // LCOV_EXCL_LINE
        };
        return is_convertible(t1, t2, ctx, mk_justification);
    }

    void check_type(expr const & e, context const & ctx) {
        set_ctx(ctx);
        update_menv(none_menv());
        expr t = infer_type_core(e, ctx);
        check_type(t, e, ctx);
    }

    void clear_cache() {
        m_cache.clear();
        m_normalizer.clear();
    }

    void clear() {
        clear_cache();
        m_menv.clear();
        m_ctx = context();
    }

    normalizer & get_normalizer() {
        return m_normalizer;
    }
};

type_checker::type_checker(ro_environment const & env):m_ptr(new imp(env)) {}
type_checker::~type_checker() {}
expr type_checker::infer_type(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * uc) {
    return m_ptr->infer_type(e, ctx, menv, uc);
}
expr type_checker::infer_type(expr const & e, context const & ctx, metavar_env const & menv, buffer<unification_constraint> & uc) {
    return m_ptr->infer_type(e, ctx, some_menv(menv), &uc);
}
expr type_checker::infer_type(expr const & e, context const & ctx, metavar_env const & menv) {
    return m_ptr->infer_type(e, ctx, some_menv(menv), nullptr);
}
expr type_checker::infer_type(expr const & e, context const & ctx) {
    return infer_type(e, ctx, none_menv(), nullptr);
}
bool type_checker::is_convertible(expr const & t1, expr const & t2, context const & ctx) {
    return m_ptr->is_convertible(t1, t2, ctx);
}
void type_checker::check_type(expr const & e, context const & ctx) {
    m_ptr->check_type(e, ctx);
}
void type_checker::clear() { m_ptr->clear(); }
normalizer & type_checker::get_normalizer() { return m_ptr->get_normalizer(); }

expr  infer_type(expr const & e, ro_environment const & env, context const & ctx) {
    return type_checker(env).infer_type(e, ctx);
}
bool is_convertible(expr const & given, expr const & expected, ro_environment const & env, context const & ctx) {
    return type_checker(env).is_convertible(given, expected, ctx);
}
}

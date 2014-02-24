/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/freset.h"
#include "util/flet.h"
#include "util/interrupt.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/kernel_exception.h"
#include "kernel/normalizer.h"
#include "kernel/instantiate.h"
#include "kernel/free_vars.h"

namespace lean {
expr pi_body_at(expr const & pi, expr const & a) {
    lean_assert(is_pi(pi));
    if (closed(binder_body(pi)))
        return binder_body(pi);
    else if (closed(a))
        return instantiate_with_closed(binder_body(pi), a);
    else
        return instantiate(binder_body(pi), a);
}

/** \brief Auxiliary functional object used to implement infer_type. */
class type_checker::imp {
    typedef expr_map<expr> cache;

    ro_environment::weak_ref  m_env;
    normalizer                m_normalizer;
    cache                     m_cache;
    name_generator *          m_name_gen;
    constraints               m_constraints; // constraints generated so far
    bool                      m_infer_only;

    ro_environment env() const { return ro_environment(m_env); }
    expr normalize(expr const & e) { return m_normalizer(e); }

#if 0
    expr check_sort(expr const & e, expr const & s) {
        if (is_sort(e))
            return e;
        expr u = normalize(e);
        if (is_sort(u))
            return u;
        if (has_metavar(u)) {
            justification jst = mk_type_expected_justification(ctx, s);
            m_uc->push_back(mk_convertible_constraint(ctx, e, TypeU1, jst));
            return u;
        }
        throw type_expected_exception(env(), ctx, s);
    }
#endif
};


#if 0
static name g_x_name("x");
/** \brief Auxiliary functional object used to implement infer_type. */
class type_checker::imp {
    expr check_type(expr const & e, expr const & s, context const & ctx) {
        if (is_type(e) || is_bool(e))
            return e;
        expr u = normalize(e, ctx, false);
        if (is_type(u) || is_bool(u))
            return u;
        if (has_metavar(u) && m_menv && m_uc) {
            justification jst = mk_type_expected_justification(ctx, s);
            m_uc->push_back(mk_convertible_constraint(ctx, e, TypeU1, jst));
            return u;
        }
        throw type_expected_exception(env(), ctx, s);
    }

    expr check_pi(expr const & e, expr const & s, context const & ctx) {
        if (is_pi(e))
            return e;
        expr r = normalize(e, ctx, false);
        if (is_pi(r))
            return r;
        if (has_metavar(r) && m_menv && m_uc) {
            // Create two fresh variables A and B,
            // and assign r == (Pi(x : A), B)
            expr A   = m_menv->mk_metavar(ctx);
            expr B   = m_menv->mk_metavar(extend(ctx, g_x_name, A));
            expr p   = mk_pi(g_x_name, A, B);
            justification jst = mk_function_expected_justification(ctx, s);
            m_uc->push_back(mk_eq_constraint(ctx, e, p, jst));
            return p;
        }
        throw function_expected_exception(env(), ctx, s);
    }

    // TODO(Leo): we should consider merging check_pi and check_sigma.
    // They are very similar
    expr check_sigma(expr const & e, expr const & s, context const & ctx) {
        if (is_sigma(e))
            return e;
        expr r = normalize(e, ctx, false);
        if (is_sigma(r))
            return r;
        if (has_metavar(r) && m_menv && m_uc) {
            // Create two fresh variables A and B,
            // and assign r == (Pi(x : A), B)
            expr A   = m_menv->mk_metavar(ctx);
            expr B   = m_menv->mk_metavar(extend(ctx, g_x_name, A));
            expr p   = mk_sigma(g_x_name, A, B);
            justification jst = mk_pair_expected_justification(ctx, s);
            m_uc->push_back(mk_eq_constraint(ctx, e, p, jst));
            return p;
        }
        throw pair_expected_exception(env(), ctx, s);
    }

    /**
       \brief Given \c t (a Pi term), this method returns the body (aka range)
       of the function space for the element e in the domain of the Pi.
    */
    expr get_pi_body(expr const & t, expr const & e) {
        lean_assert(is_pi(t));
        if (is_arrow(t))
            return lower_free_vars(abst_body(t), 1, 1);
        else
            return instantiate(abst_body(t), e);
    }

    expr get_range(expr t, expr const & e, context const & ctx) {
        unsigned num = num_args(e);
        for (unsigned i = 1; i < num; i++) {
            expr const & a = arg(e, i);
            if (is_pi(t)) {
                t = get_pi_body(t, a);
            } else {
                t = normalize(t, ctx, false);
                if (is_pi(t)) {
                    t = get_pi_body(t, a);
                } else if (has_metavar(t) && m_menv && m_uc) {
                    // Create two fresh variables A and B,
                    // and assign r == (Pi(x : A), B)
                    expr A   = m_menv->mk_metavar(ctx);
                    expr B   = m_menv->mk_metavar(extend(ctx, g_x_name, A));
                    expr p   = mk_pi(g_x_name, A, B);
                    justification jst = mk_function_expected_justification(ctx, e);
                    m_uc->push_back(mk_eq_constraint(ctx, t, p, jst));
                    t        = get_pi_body(p, a);
                } else {
                    throw function_expected_exception(env(), ctx, e);
                }
            }
        }
        return t;
    }

    expr save_result(expr const & e, expr const & r, bool shared) {
        if (shared)
            m_cache[e] = r;
        return r;
    }

    expr infer_type_core(expr const & e, context const & ctx) {
        check_system("type checker");
        // cheap cases, we do not cache results
        switch (e.kind()) {
        case expr_kind::MetaVar:
            if (m_menv) {
                if (m_menv->is_assigned(e))
                    return infer_type_core(*(m_menv->get_subst(e)), ctx);
                else
                    return m_menv->get_type(e);
            } else {
                throw unexpected_metavar_occurrence(env(), e);
            }
        case expr_kind::Constant: {
            if (const_type(e)) {
                return *const_type(e);
            } else {
                object const & obj = env()->get_object(const_name(e));
                if (obj.has_type())
                    return obj.get_type();
                else
                    throw has_no_type_exception(env(), e);
            }
            break;
        }
        case expr_kind::Var: {
            auto const & entry = lookup(ctx, var_idx(e));
            if (entry.get_domain())
                return lift_free_vars(*(entry.get_domain()), var_idx(e) + 1);
            // Remark: the case where ce.get_domain() is not
            // available is not considered cheap.
            break;
        }
        case expr_kind::Value:
            if (m_infer_only) {
                return to_value(e).get_type();
            } else {
                name const & n = to_value(e).get_name();
                object obj = env()->get_object(n);
                if ((obj.is_builtin() && obj.get_value() == e) || (obj.is_builtin_set() && obj.in_builtin_set(e))) {
                    return to_value(e).get_type();
                } else {
                    throw invalid_builtin_value_reference(env(), e);
                }
            }
        case expr_kind::Type:
            return mk_type(ty_level(e) + 1);
        case expr_kind::App: case expr_kind::Lambda:
        case expr_kind::Pi:  case expr_kind::Let:
        case expr_kind::Sigma: case expr_kind::Proj:
        case expr_kind::Pair:
            break; // expensive cases
        }

        bool shared = false;
        if (is_shared(e)) {
            shared = true;
            auto it = m_cache.find(e);
            if (it != m_cache.end())
                return it->second;
        }

        expr r;
        switch (e.kind()) {
        case expr_kind::MetaVar: case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value:
            lean_unreachable(); // LCOV_EXCL_LINE;
        case expr_kind::Var: {
            unsigned i = var_idx(e);
            auto p = lookup_ext(ctx, i);
            context_entry const & def = p.first;
            context const & def_ctx   = p.second;
            lean_assert(ctx.size() > def_ctx.size());
            lean_assert(!def.get_domain()); // was handled as cheap
            optional<expr> const & b = def.get_body();
            lean_assert(b);
            expr t = infer_type_core(*b, def_ctx);
            r = lift_free_vars(t, var_idx(e) + 1);
            break;
        }
        case expr_kind::App:
            if (m_infer_only) {
                expr const & f = arg(e, 0);
                expr f_t = infer_type_core(f, ctx);
                r = get_range(f_t, e, ctx);
            } else {
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
                    // thunk for creating justification object if needed
                    auto mk_justification = [&](){ return mk_app_type_match_justification(ctx, e, i); };
                    if (!is_convertible(c_t, abst_domain(f_t), ctx, mk_justification))
                        throw app_type_mismatch_exception(env(), ctx, e, i, arg_types.size(), arg_types.data());
                    f_t = pi_body_at(f_t, c);
                    i++;
                    if (i == num) {
                        r = f_t;
                        break;
                    }
                    f_t = check_pi(f_t, e, ctx);
                }
            }
            break;
        case expr_kind::Pair:
            if (m_infer_only) {
                r = pair_type(e);
            } else {
                expr const & t = pair_type(e);
                expr sig       = check_sigma(t, t, ctx);
                expr f_t       = infer_type_core(pair_first(e), ctx);
                expr s_t       = infer_type_core(pair_second(e), ctx);
                auto mk_fst_justification = [&]() { return mk_pair_type_match_justification(ctx, e, true); };
                if (!is_convertible(f_t, abst_domain(sig), ctx, mk_fst_justification))
                    throw pair_type_mismatch_exception(env(), ctx, e, true, f_t, sig);
                auto mk_snd_justification = [&]() { return mk_pair_type_match_justification(ctx, e, false); };
                expr expected  = instantiate(abst_body(sig), pair_first(e));
                if (!is_convertible(s_t, expected, ctx, mk_snd_justification)) {
                    throw pair_type_mismatch_exception(env(), ctx, e, false, s_t, sig);
                }
                r = sig;
            }
            break;
        case expr_kind::Proj: {
            expr t = check_sigma(infer_type_core(proj_arg(e), ctx), e, ctx);
            if (proj_first(e)) {
                r = abst_domain(t);
            } else {
                expr const & b = abst_body(t);
                if (closed(b))
                    r = b;
                else
                    r = instantiate(b, mk_proj1(proj_arg(e)));
            }
            break;
        }
        case expr_kind::Lambda:
            if (!m_infer_only) {
                expr d = infer_type_core(abst_domain(e), ctx);
                check_type(d, abst_domain(e), ctx);
            }
            {
                freset<cache> reset(m_cache);
                r = mk_pi(abst_name(e), abst_domain(e), infer_type_core(abst_body(e), extend(ctx, abst_name(e), abst_domain(e))));
            }
            break;
        case expr_kind::Sigma: case expr_kind::Pi: {
            expr t1  = check_type(infer_type_core(abst_domain(e), ctx), abst_domain(e), ctx);
            if (is_bool(t1))
                t1 = Type();
            expr t2;
            context new_ctx = extend(ctx, abst_name(e), abst_domain(e));
            {
                freset<cache> reset(m_cache);
                t2 = check_type(infer_type_core(abst_body(e), new_ctx), abst_body(e), new_ctx);
            }
            if (is_bool(t2)) {
                if (is_pi(e)) {
                    r = Bool;
                    break;
                } else {
                    t2 = Type();
                }
            }
            if (is_type(t1) && is_type(t2)) {
                r = mk_type(max(ty_level(t1), ty_level(t2)));
            } else {
                lean_assert(m_uc);
                justification jst = mk_max_type_justification(ctx, e);
                r = m_menv->mk_metavar(ctx);
                m_uc->push_back(mk_max_constraint(new_ctx, lift_free_vars(t1, 0, 1), t2, r, jst));
            }
            break;
        }
        case expr_kind::Let: {
            optional<expr> lt;
            if (m_infer_only) {
                lt = let_type(e);
            } else {
                if (let_type(e)) {
                    expr value_ty = infer_type_core(let_value(e), ctx);
                    expr ty       = infer_type_core(*let_type(e), ctx);
                    check_type(ty, *let_type(e), ctx); // check if it is really a type
                    // thunk for creating justification object if needed
                    auto mk_justification = [&](){ return mk_def_type_match_justification(ctx, let_name(e), let_value(e)); };
                    if (!is_convertible(value_ty, *let_type(e), ctx, mk_justification))
                        throw def_type_mismatch_exception(env(), ctx, let_name(e), *let_type(e), let_value(e), value_ty);
                    lt = let_type(e);
                } else {
                    lt = infer_type_core(let_value(e), ctx);
                }
            }
            {
                freset<cache> reset(m_cache);
                expr t = infer_type_core(let_body(e), extend(ctx, let_name(e), lt, let_value(e)));
                r = instantiate(t, let_value(e));
            }
            break;
        }}
        return save_result(e, r, shared);
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
        expr new_given    = normalize(given, ctx, false);
        expr new_expected = normalize(expected, ctx, false);
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

    struct set_infer_only {
        imp & m_ref;
        bool  m_old_infer_only;
        set_infer_only(imp & r, bool flag):m_ref(r), m_old_infer_only(m_ref.m_infer_only) {
            if (m_ref.m_infer_only != flag)
                m_ref.clear_cache();
            m_ref.m_infer_only = flag;
        }
        ~set_infer_only() {
            if (m_ref.m_infer_only != m_old_infer_only)
                m_ref.clear_cache();
            m_ref.m_infer_only = m_old_infer_only;
        }
    };

public:
    imp(ro_environment const & env, bool infer_only):
        m_env(env),
        m_normalizer(env) {
        m_uc              = nullptr;
        m_infer_only      = infer_only;
    }

    expr infer_check(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * uc,
                     bool infer_only) {
        clear_cache(); // temp hack
        set_infer_only set(*this, infer_only);
        set_ctx(ctx);
        update_menv(menv);
        flet<unification_constraints*> set_uc(m_uc, uc);
        return infer_type_core(e, ctx);
    }

    expr infer_type(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * uc) {
        return infer_check(e, ctx, menv, uc, true);
    }

    expr check(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * uc) {
        return infer_check(e, ctx, menv, uc, false);
    }

    bool is_convertible(expr const & t1, expr const & t2, context const & ctx, optional<metavar_env> const & menv) {
        set_ctx(ctx);
        update_menv(menv);
        auto mk_justification = [](){
            lean_unreachable(); return justification(); // LCOV_EXCL_LINE
        };
        return is_convertible(t1, t2, ctx, mk_justification);
    }

    bool is_definitionally_equal(expr const & t1, expr const & t2, context const & ctx, optional<metavar_env> const & menv) {
        set_ctx(ctx);
        update_menv(menv);
        if (t1 == t2)
            return true;
        expr new_t1 = normalize(t1, ctx, false);
        expr new_t2 = normalize(t2, ctx, false);
        return new_t1 == new_t2;
    }

    void check_type(expr const & e, context const & ctx) {
        set_ctx(ctx);
        update_menv(none_menv());
        expr t = infer_type_core(e, ctx);
        check_type(t, e, ctx);
    }

    bool is_proposition(expr const & e, context const & ctx, optional<metavar_env> const & menv) {
        // Catch easy cases
        switch (e.kind()) {
        case expr_kind::Lambda: case expr_kind::Type:
            return false;
        case expr_kind::Pi:
            return is_proposition(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)), menv);
        default:
            break;
        }
        expr t = infer_type(e, ctx, menv, nullptr);
        if (is_bool(t))
            return true;
        else
            return is_bool(normalize(t, ctx, false));
    }

    expr ensure_pi(expr const & e, context const & ctx, optional<metavar_env> const & menv) {
        set_ctx(ctx);
        update_menv(menv);
        try {
            return check_pi(e, expr(), ctx);
        } catch (exception &) {
            throw exception("internal bug, expression is not a Pi");
        }
    }

    expr ensure_sigma(expr const & e, context const & ctx, optional<metavar_env> const & menv) {
        set_ctx(ctx);
        update_menv(menv);
        try {
            return check_sigma(e, expr(), ctx);
        } catch (exception &) {
            throw exception("internal bug, expression is not a Sigma");
        }
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

type_checker::type_checker(ro_environment const & env, bool infer_only):m_ptr(new imp(env, infer_only)) {}
type_checker::~type_checker() {}
expr type_checker::infer_type(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * uc) {
    return m_ptr->infer_type(e, ctx, menv, uc);
}
expr type_checker::infer_type(expr const & e, context const & ctx, metavar_env const & menv, buffer<unification_constraint> & uc) {
    return m_ptr->infer_type(e, ctx, some_menv(menv), &uc);
}
expr type_checker::infer_type(expr const & e, context const & ctx, ro_metavar_env const & menv) {
    // metavariable environment is not updated when unification constraints are not provided
    return infer_type(e, ctx, some_menv(menv.to_rw()), nullptr);
}
expr type_checker::infer_type(expr const & e, context const & ctx, optional<ro_metavar_env> const & menv) {
    return infer_type(e, ctx, ro_metavar_env::to_rw(menv), nullptr);
}
expr type_checker::infer_type(expr const & e, context const & ctx) {
    return infer_type(e, ctx, none_menv(), nullptr);
}
expr type_checker::check(expr const & e, context const & ctx, optional<metavar_env> const & menv, buffer<unification_constraint> * uc) {
    return m_ptr->check(e, ctx, menv, uc);
}
expr type_checker::check(expr const & e, context const & ctx, metavar_env const & menv, buffer<unification_constraint> & uc) {
    return m_ptr->check(e, ctx, some_menv(menv), &uc);
}
expr type_checker::check(expr const & e, context const & ctx, ro_metavar_env const & menv) {
    // metavariable environment is not updated when unification constraints are not provided
    return check(e, ctx, some_menv(menv.to_rw()), nullptr);
}
expr type_checker::check(expr const & e, context const & ctx) {
    return check(e, ctx, none_menv(), nullptr);
}
bool type_checker::is_convertible(expr const & t1, expr const & t2, context const & ctx, optional<ro_metavar_env> const & menv) {
    return m_ptr->is_convertible(t1, t2, ctx, ro_metavar_env::to_rw(menv));
}
bool type_checker::is_convertible(expr const & t1, expr const & t2, context const & ctx) {
    return m_ptr->is_convertible(t1, t2, ctx, none_menv());
}
bool type_checker::is_definitionally_equal(expr const & t1, expr const & t2, context const & ctx, optional<ro_metavar_env> const & menv) {
    return m_ptr->is_definitionally_equal(t1, t2, ctx, ro_metavar_env::to_rw(menv));
}
bool type_checker::is_definitionally_equal(expr const & t1, expr const & t2, context const & ctx) {
    return m_ptr->is_definitionally_equal(t1, t2, ctx, none_menv());
}
void type_checker::check_type(expr const & e, context const & ctx) {
    m_ptr->check_type(e, ctx);
}
expr type_checker::ensure_pi(expr const & e, context const & ctx, optional<ro_metavar_env> const & menv) {
    return m_ptr->ensure_pi(e, ctx, ro_metavar_env::to_rw(menv));
}
expr type_checker::ensure_pi(expr const & e, context const & ctx) {
    return m_ptr->ensure_pi(e, ctx, none_menv());
}
expr type_checker::ensure_sigma(expr const & e, context const & ctx, optional<ro_metavar_env> const & menv) {
    return m_ptr->ensure_sigma(e, ctx, ro_metavar_env::to_rw(menv));
}
expr type_checker::ensure_sigma(expr const & e, context const & ctx) {
    return m_ptr->ensure_sigma(e, ctx, none_menv());
}
bool type_checker::is_proposition(expr const & e, context const & ctx, optional<ro_metavar_env> const & menv) {
    return m_ptr->is_proposition(e, ctx, ro_metavar_env::to_rw(menv));
}
bool type_checker::is_proposition(expr const & e, context const & ctx) {
    return is_proposition(e, ctx, none_ro_menv());
}
bool type_checker::is_proposition(expr const & e, context const & ctx, ro_metavar_env const & menv) {
    return is_proposition(e, ctx, some_ro_menv(menv));
}
bool type_checker::is_flex_proposition(expr e, context ctx, optional<ro_metavar_env> const & menv) {
    while (is_pi(e)) {
        ctx = extend(ctx, abst_name(e), abst_domain(e));
        e   = abst_body(e);
    }
    return is_proposition(e, ctx, menv);
}
bool type_checker::is_flex_proposition(expr const & e, context const & ctx, ro_metavar_env const & menv) {
    return is_flex_proposition(e, ctx, some_ro_menv(menv));
}
bool type_checker::is_flex_proposition(expr const & e, context const & ctx) {
    return is_flex_proposition(e, ctx, none_ro_menv());
}
void type_checker::clear() { m_ptr->clear(); }
normalizer & type_checker::get_normalizer() { return m_ptr->get_normalizer(); }
expr  type_check(expr const & e, ro_environment const & env, context const & ctx) {
    return type_checker(env).check(e, ctx);
}
bool is_convertible(expr const & given, expr const & expected, ro_environment const & env, context const & ctx) {
    return type_checker(env).is_convertible(given, expected, ctx);
}
bool is_proposition(expr const & e, ro_environment const & env, context const & ctx, optional<ro_metavar_env> const & menv) {
    return type_checker(env).is_proposition(e, ctx, menv);
}
bool is_proposition(expr const & e, ro_environment const & env, context const & ctx, ro_metavar_env const & menv) {
    return is_proposition(e, env, ctx, some_ro_menv(menv));
}
bool is_proposition(expr const & e, ro_environment const & env, context const & ctx) {
    return is_proposition(e, env, ctx, none_ro_menv());
}
#endif
}

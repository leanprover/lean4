/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "type_check.h"
#include "scoped_map.h"
#include "environment.h"
#include "normalize.h"
#include "instantiate.h"
#include "builtin.h"
#include "free_vars.h"
#include "exception.h"
#include "trace.h"

namespace lean {
bool is_convertible_core(expr const & expected, expr const & given, environment const & env) {
    if (expected == given)
        return true;
    expr const * e = &expected;
    expr const * g = &given;
    while (true) {
        if (is_type(*e) && is_type(*g)) {
            if (env.is_ge(ty_level(*e), ty_level(*g)))
                return true;
        }
        if (is_pi(*e) && is_pi(*g) && abst_domain(*e) == abst_domain(*g)) {
            e = &abst_body(*e);
            g = &abst_body(*g);
        } else {
            return false;
        }
    }
}

bool is_convertible(expr const & expected, expr const & given, environment const & env, context const & ctx) {
    lean_trace("is_convertible", tout << expected << "\n" << given << "\n" << ctx << "\n";);
    if (is_convertible_core(expected, given, env))
        return true;
    expr e_n = normalize(expected, env, ctx);
    expr g_n = normalize(given, env, ctx);
    return is_convertible_core(e_n, g_n, env);
}

struct infer_type_fn {
    typedef scoped_map<expr, expr, expr_hash, expr_eqp> cache;

    environment const & m_env;
    cache               m_cache;

    expr lookup(context const & c, unsigned i) {
        auto p = lookup_ext(c, i);
        context_entry const & def = p.first;
        context const & def_c     = p.second;
        lean_assert(length(c) > length(def_c));
        return lift_free_vars(def.get_domain(), length(c) - length(def_c));
    }

    expr_formatter & fmt() { return m_env.get_formatter(); }

    format nl_indent(format const & f) { return fmt().nest(format{line(), f}); }

    void throw_error [[ noreturn ]] (expr const & src, format const & msg) {
        throw_exception(m_env.get_locator(), src, msg);
    }

    /** \brief Include context (if not empty) in the formatted message */
    void push_context(format & msg, context const & ctx) {
        if (!is_empty(ctx)) {
            msg += format{format("in context: "), nl_indent(pp(fmt(), ctx)), line()};
        }
    }

    void throw_type_expected_error [[ noreturn ]] (expr const & t, context const & ctx) {
        context ctx2 = sanitize_names(ctx, t);
        format msg = format("type expected, ");
        push_context(msg, ctx2);
        msg += format{format("got:"), nl_indent(fmt()(t, ctx2))};
        throw_error(t, msg);
    }

    void throw_function_expected_error [[ noreturn ]] (expr const & s, context const & ctx) {
        context ctx2 = sanitize_names(ctx, s);
        format msg = format("function expected, ");
        push_context(msg, ctx2);
        msg += format{format("got:"), nl_indent(fmt()(s, ctx2))};
        throw_error(s, msg);
    }

    void throw_type_mismatch_error [[ noreturn ]] (expr const & app, unsigned arg_pos,
                                                   expr const & expected, expr const & given, context const & ctx) {
        context ctx2 = sanitize_names(ctx, {app, expected, given});
        format msg = format{format("type mismatch at argument "), format(arg_pos), space(), format("of"),
                            nl_indent(fmt()(app, ctx2)), line()};
        push_context(msg, ctx2);
        msg += format{format("expected type:"), nl_indent(fmt()(expected, ctx2)), line(), format("given type:"), nl_indent(fmt()(given, ctx2))};
        throw_error(arg(app, arg_pos), msg);
    }

    level infer_universe(expr const & t, context const & ctx) {
        lean_trace("type_check", tout << "infer universe\n" << t << "\n";);
        expr u = normalize(infer_type(t, ctx), m_env, ctx);
        if (is_type(u))
            return ty_level(u);
        if (u == Bool)
            return level();
        throw_type_expected_error(t, ctx);
    }

    expr check_pi(expr const & e, expr const & s, context const & ctx) {
        if (is_pi(e))
            return e;
        expr r = normalize(e, m_env, ctx);
        if (is_pi(r))
            return r;
        throw_function_expected_error(s, ctx);
    }

    expr infer_pi(expr const & e, context const & ctx) {
        return check_pi(infer_type(e, ctx), e, ctx);
    }

    expr infer_type(expr const & e, context const & ctx) {
        lean_trace("type_check", tout << "infer type\n" << e << "\n" << ctx << "\n";);

        bool shared = false;
        if (true && is_shared(e)) {
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
                    throw_type_mismatch_error(e, i, abst_domain(f_t), c_t, ctx);
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

    infer_type_fn(environment const & env):
        m_env(env) {
    }

    expr operator()(expr const & e, context const & ctx) {
        return infer_type(e, ctx);
    }
};

expr  infer_type(expr const & e, environment const & env, context const & ctx) {
    return infer_type_fn(env)(e, ctx);
}

level infer_universe(expr const & t, environment const & env, context const & ctx) {
    return infer_type_fn(env).infer_universe(t, ctx);
}
}

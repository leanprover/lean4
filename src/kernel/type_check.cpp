/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include "type_check.h"
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
        }
        else {
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
    environment const & m_env;

    expr lookup(context const & c, unsigned i) {
        context const & def_c = ::lean::lookup(c, i);
        lean_assert(length(c) >= length(def_c));
        lean_assert(length(def_c) > 0);
        return lift_free_vars(head(def_c).get_type(), length(c) - (length(def_c) - 1));
    }

    level infer_universe(expr const & t, context const & ctx) {
        lean_trace("type_check", tout << "infer universe\n" << t << "\n";);
        expr u = normalize(infer_type(t, ctx), m_env, ctx);
        if (is_type(u))
            return ty_level(u);
        if (is_bool_type(u))
            return level();
        std::ostringstream buffer;
        buffer << "type expected, ";
        if (!empty(ctx))
            buffer << "in context:\n" << ctx << "\n";
        buffer << "got:\n" << t;
        throw exception(buffer.str());
    }

    expr check_pi(expr const & e, context const & ctx) {
        if (is_pi(e))
            return e;
        expr r = normalize(e, m_env, ctx);
        if (is_pi(r))
            return r;
        std::ostringstream buffer;
        buffer << "function expected, ";
        if (!empty(ctx))
            buffer << "in context:\n" << ctx << "\n";
        buffer << "got:\n" << e;
        throw exception(buffer.str());
    }

    expr infer_pi(expr const & e, context const & ctx) {
        return check_pi(infer_type(e, ctx), ctx);
    }

    expr infer_type(expr const & e, context const & ctx) {
        lean_trace("type_check", tout << "infer type\n" << e << "\n" << ctx << "\n";);
        switch (e.kind()) {
        case expr_kind::Constant:
            return m_env.get_object(const_name(e)).get_type();
        case expr_kind::Var:      return lookup(ctx, var_idx(e));
        case expr_kind::Type:     return mk_type(ty_level(e) + 1);
        case expr_kind::App: {
            expr f_t     = infer_pi(arg(e, 0), ctx);
            unsigned i   = 1;
            unsigned num = num_args(e);
            lean_assert(num >= 2);
            while (true) {
                expr const & c = arg(e, i);
                expr c_t       = infer_type(c, ctx);
                if (!is_convertible(abst_domain(f_t), c_t, m_env, ctx)) {
                    std::ostringstream buffer;
                    buffer << "type mismatch at argument " << i << " of\n" << e
                           << "\nexpected type:\n" << abst_domain(f_t)
                           << "\ngiven type:\n" << c_t;
                    if (!empty(ctx))
                        buffer << "\nin context:\n" << ctx;
                    throw exception(buffer.str());
                }
                f_t = instantiate(abst_body(f_t), c);
                i++;
                if (i == num)
                    return f_t;
                check_pi(f_t, ctx);
            }
        }
        case expr_kind::Eq:
            infer_type(eq_lhs(e), ctx);
            infer_type(eq_rhs(e), ctx);
            return mk_bool_type();
        case expr_kind::Lambda: {
            infer_universe(abst_domain(e), ctx);
            expr t = infer_type(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            return mk_pi(abst_name(e), abst_domain(e), t);
        }
        case expr_kind::Pi: {
            level l1 = infer_universe(abst_domain(e), ctx);
            level l2 = infer_universe(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
            return mk_type(max(l1, l2));
        }
        case expr_kind::Let:
            return infer_type(let_body(e), extend(ctx, let_name(e), infer_type(let_value(e), ctx), let_value(e)));
        case expr_kind::Value:
            return to_value(e).get_type();
        }
        lean_unreachable();
        return e;
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

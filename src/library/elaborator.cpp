/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "elaborator.h"
#include "free_vars.h"
#include "beta.h"
#include "instantiate.h"
#include "builtin.h"
#include "exception.h"

namespace lean {

expr elaborator::lookup(context const & c, unsigned i) {
    auto p = lookup_ext(c, i);
    context_entry const & def = p.first;
    context const & def_c     = p.second;
    lean_assert(length(c) > length(def_c));
    return lift_free_vars(def.get_domain(), length(c) - length(def_c));
}

elaborator::elaborator(environment & env):
    m_env(env), m_metaenv(env) {
}

void elaborator::unify(expr const & e1, expr const & e2, context const & ctx) {
    if (has_metavar(e1) || has_metavar(e2)) {
        // std::cout << "UNIFY: " << e1 << " <--> " << e2 << "\n";
        m_metaenv.unify(e1, e2, ctx);
    }
}

expr elaborator::check_pi(expr const & e, context const & ctx) {
    if (!e) {
        // e is the type of a metavariable.
        // approx: assume it is Type()
        return Type();
    } else if (is_pi(e)) {
        return e;
    } else {
        expr r = head_reduce(e, m_env);
        if (!is_eqp(r, e)) {
            return check_pi(r, ctx);
        } else if (is_var(e)) {
            auto p = lookup_ext(ctx, var_idx(e));
            context_entry const & entry = p.first;
            context const & entry_ctx   = p.second;
            if (entry.get_body()) {
                return lift_free_vars(check_pi(entry.get_body(), entry_ctx),
                                      length(ctx) - length(entry_ctx));
            }
        }
        throw exception("function expected");
    }
}

level elaborator::check_universe(expr const & e, context const & ctx) {
    if (!e) {
        // e is the type of a metavariable
        // approx: assume it is level 0
        return level();
    } else if (is_type(e)) {
        return ty_level(e);
    } else {
        expr r = head_reduce(e, m_env);
        if (!is_eqp(r, e)) {
            return check_universe(r, ctx);
        } else if (is_var(e)) {
            auto p = lookup_ext(ctx, var_idx(e));
            context_entry const & entry = p.first;
            context const & entry_ctx   = p.second;
            if (entry.get_body()) {
                return check_universe(entry.get_body(), entry_ctx);
            }
        }
        throw exception("type expected");
    }
}

/**
   \brief Given e and a context, try to instantiate the
   meta-variables in \c e. Return an inferred type for \c e.
*/
expr elaborator::process(expr const & e, context const & ctx) {
    switch (e.kind()) {
    case expr_kind::Constant:
        if (is_metavar(e)) {
            return expr();
        } else {
            return m_env.get_object(const_name(e)).get_type();
        }
    case expr_kind::Var:
        return lookup(ctx, var_idx(e));
    case expr_kind::Type:
        return mk_type(ty_level(e) + 1);
    case expr_kind::Value:
        return to_value(e).get_type();
    case expr_kind::App: {
        buffer<expr> types;
        unsigned num = num_args(e);
        for (unsigned i = 0; i < num; i++) {
            types.push_back(process(arg(e,i), ctx));
        }
        // TODO: handle overload in args[0]
        expr f_t = types[0];
        if (!f_t) {
            throw exception("invalid use of placeholder, the function must be provided to an application");
        }
        for (unsigned i = 1; i < num; i++) {
            f_t = check_pi(f_t, ctx);
            if (types[i])
                unify(abst_domain(f_t), types[i], ctx);
            f_t = instantiate(abst_body(f_t), arg(e, i));
        }
        return f_t;
    }
    case expr_kind::Eq: {
        process(eq_lhs(e), ctx);
        process(eq_rhs(e), ctx);
        return mk_bool_type();
    }
    case expr_kind::Pi: {
        expr dt = process(abst_domain(e), ctx);
        expr bt = process(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
        return mk_type(max(check_universe(dt, ctx), check_universe(bt, ctx)));
    }
    case expr_kind::Lambda: {
        expr dt = process(abst_domain(e), ctx);
        expr bt = process(abst_body(e), extend(ctx, abst_name(e), abst_domain(e)));
        return mk_pi(abst_name(e), abst_domain(e), bt);
    }
    case expr_kind::Let: {
        expr lt = process(let_value(e), ctx);
        return process(let_body(e), extend(ctx, let_name(e), lt, let_value(e)));
    }}
    lean_unreachable();
    return expr();
}

expr elaborator::operator()(expr const & e) {
    expr t = process(e, context());
    return m_metaenv.instantiate_metavars(e);
}
}

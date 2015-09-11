/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/replace_visitor.h"
#include "compiler/eta_expansion.h"

namespace lean {
class eta_expand_fn : public replace_visitor {
    environment  m_env;
    type_checker m_tc;

    optional<expr> expand_core(expr const & e) {
        lean_assert(!is_lambda(e));
        expr t = m_tc.whnf(m_tc.infer(e).first).first;
        if (!is_pi(t))
            return none_expr();
        expr r = mk_lambda(name("x"), binding_domain(t), mk_app(e, mk_var(0)));
        return some_expr(visit(r));
    }

    expr expand(expr const & e) {
        if (auto r = expand_core(e))
            return *r;
        else
            return e;
    }

    virtual expr visit_var(expr const &) { lean_unreachable(); }

    virtual expr visit_meta(expr const &) { lean_unreachable(); }

    virtual expr visit_macro(expr const & e) {
        if (auto r = expand_core(e))
            return *r;
        else
            return replace_visitor::visit_macro(e);
    }

    virtual expr visit_constant(expr const & e) { return expand(e); }

    virtual expr visit_local(expr const & e) { return expand(e); }

    virtual expr visit_app(expr const & e) {
        if (auto r = expand_core(e)) {
            return *r;
        } else {
            buffer<expr> args;
            expr f = get_app_args(e, args);
            bool modified = false;
            for (unsigned i = 0; i < args.size(); i++) {
                expr arg     = args[i];
                expr new_arg = visit(arg);
                if (!is_eqp(arg, new_arg))
                    modified = true;
                args[i] = new_arg;
            }
            if (!modified)
                return e;
            else
                return mk_app(f, args);
        }
    }

    virtual expr visit_binding(expr const & b) {
        expr new_domain = visit(binding_domain(b));
        expr l          = mk_local(m_tc.mk_fresh_name(), new_domain);
        expr new_body   = abstract_local(visit(instantiate(binding_body(b), l)), l);
        return update_binding(b, new_domain, new_body);
    }

public:
    eta_expand_fn(environment const & env):m_env(env), m_tc(env, name_generator()) {}
};

expr eta_expand(environment const & env, expr const & e) {
    return eta_expand_fn(env)(e);
}
}

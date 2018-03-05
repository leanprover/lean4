/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/replace_visitor_with_tc.h"
namespace lean {
expr replace_visitor_with_tc::visit_lambda_pi_let(bool is_lam, expr const & e) {
    type_context_old::tmp_locals locals(m_ctx);
    expr t = e;
    while (true) {
        if ((is_lam && is_lambda(t)) || (!is_lam && is_pi(t))) {
            expr d = instantiate_rev(binding_domain(t), locals.size(), locals.data());
            d = visit(d);
            locals.push_local(binding_name(t), d, binding_info(t));
            t = binding_body(t);
        } else if (is_let(t)) {
            expr d = instantiate_rev(let_type(t), locals.size(), locals.data());
            expr v = instantiate_rev(let_value(t), locals.size(), locals.data());
            d = visit(d);
            v = visit(v);
            locals.push_let(let_name(t), d, v);
            t = let_body(t);
        } else {
            break;
        }
    }
    t = instantiate_rev(t, locals.size(), locals.data());
    t = visit(t);
    return is_lam ? copy_tag(e, locals.mk_lambda(t)) : copy_tag(e, locals.mk_pi(t));
}

expr replace_visitor_with_tc::visit_app(expr const & e) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    expr new_fn   = visit(fn);
    bool modified = !is_eqp(fn, new_fn);
    for (expr & arg : args) {
        expr new_arg = visit(arg);
        if (!is_eqp(new_arg, arg))
            modified = true;
        arg = new_arg;
    }
    if (!modified)
        return e;
    else
        return copy_tag(e, mk_app(new_fn, args));
}
}

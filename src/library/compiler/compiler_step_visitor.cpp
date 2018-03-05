/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/quote.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/comp_irrelevant.h"

namespace lean {
/*
  Remark: we don't need typeclass resolution in the compiler.
*/
static local_context mk_local_context_without_local_instances() {
    local_context lctx;
    lctx.freeze_local_instances(local_instances());
    return lctx;
}

compiler_step_visitor::compiler_step_visitor(environment const & env, abstract_context_cache & cache):
    m_env(env),
    m_ctx(env, metavar_context(), mk_local_context_without_local_instances(), cache, transparency_mode::All) {
}

compiler_step_visitor::~compiler_step_visitor() {
}

expr compiler_step_visitor::visit_lambda_let(expr const & e) {
    type_context_old::tmp_locals locals(m_ctx);
    expr t = e;
    while (true) {
        /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
        if (is_lambda(t)) {
            expr d = instantiate_rev(binding_domain(t), locals.size(), locals.data());
            locals.push_local(binding_name(t), d, binding_info(t));
            t = binding_body(t);
        } else if (is_let(t)) {
            expr d = instantiate_rev(let_type(t), locals.size(), locals.data());
            expr v = visit(instantiate_rev(let_value(t), locals.size(), locals.data()));
            locals.push_let(let_name(t), d, v);
            t = let_body(t);
        } else {
            break;
        }
    }
    t = instantiate_rev(t, locals.size(), locals.data());
    t = visit(t);
    return copy_tag(e, locals.mk_lambda(t));
}

expr compiler_step_visitor::visit_lambda(expr const & e) {
    return visit_lambda_let(e);
}

expr compiler_step_visitor::visit_let(expr const & e) {
    return visit_lambda_let(e);
}

expr compiler_step_visitor::visit_macro(expr const & e) {
    if (is_marked_as_comp_irrelevant(e))
        return e;
    else
        return replace_visitor::visit_macro(e);
}

expr compiler_step_visitor::visit_app(expr const & e) {
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

/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/locals.h"
#include "library/compiler/procedure.h"
#include "library/compiler/compiler_step_visitor.h"

namespace lean {
class elim_unused_lets_fn : public compiler_step_visitor {
    virtual expr visit_lambda(expr const & e) override {
        type_context_old::tmp_locals locals(m_ctx);
        expr t = e;
        while (is_lambda(t)) {
            expr d = instantiate_rev(binding_domain(t), locals.size(), locals.data());
            locals.push_local(binding_name(t), d, binding_info(t));
            t = binding_body(t);
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);
        return copy_tag(e, locals.mk_lambda(t));
    }

    virtual expr visit_let(expr const & e) override {
        type_context_old::tmp_locals locals(m_ctx);
        collected_locals used_locals;
        expr t = e;
        while (is_let(t)) {
            expr d = instantiate_rev(let_type(t), locals.size(), locals.data());
            expr v = visit(instantiate_rev(let_value(t), locals.size(), locals.data()));
            collect_locals(d, used_locals);
            collect_locals(v, used_locals);
            locals.push_let(let_name(t), d, v);
            t = let_body(t);
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);
        collect_locals(t, used_locals);
        buffer<expr> new_locals;
        for (expr const & l : locals.as_buffer()) {
            if (used_locals.contains(l))
                new_locals.push_back(l);
        }
        return copy_tag(e, m_ctx.mk_lambda(new_locals, t));
    }
public:
    elim_unused_lets_fn(environment const & env, abstract_context_cache & cache):compiler_step_visitor(env, cache) {}
};

void elim_unused_lets(environment const & env, abstract_context_cache & cache, buffer<procedure> & procs) {
    elim_unused_lets_fn fn(env, cache);
    for (auto & proc : procs)
        proc.m_code = fn(proc.m_code);
}
}

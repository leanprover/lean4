/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "library/locals.h"
#include "library/util.h"
#include "compiler/fresh_constant.h"
#include "compiler/comp_irrelevant.h"
#include "compiler/compiler_step_visitor.h"

namespace lean {
class lambda_lifting_fn : public compiler_step_visitor {
    buffer<name> & m_new_decls;
    bool           m_trusted;
protected:
    expr declare_aux_def(expr const & value) {
        pair<environment, name> ep = mk_fresh_constant(m_env);
        m_env  = ep.first;
        name n = ep.second;
        m_new_decls.push_back(n);
        level_param_names ps = to_level_param_names(collect_univ_params(value));
        /* We should use a new type checker because m_env is updated by this object.
           It is safe to use type_checker because value does not contain local_decl_ref objects. */
        type_checker tc(m_env);
        expr type         = tc.infer(value);
        bool use_conv_opt = false;
        declaration new_decl = mk_definition(m_env, n, ps, type, value, use_conv_opt, m_trusted);
        m_env = m_env.add(check(m_env, new_decl));
        return mk_constant(n, param_names_to_levels(ps));
    }

    typedef rb_map<unsigned, local_decl, unsigned_rev_cmp> idx2decls;

    void collect_locals(expr const & e, idx2decls & r) {
        local_context const & lctx = m_ctx.lctx();
        for_each(e, [&](expr const & e, unsigned) {
                if (is_local_decl_ref(e)) {
                    local_decl d = *lctx.get_local_decl(e);
                    r.insert(d.get_idx(), d);
                }
                return true;
            });
    }

    expr visit_lambda_core(expr const & e) {
        type_context::tmp_locals locals(m_ctx);
        expr t = e;
        while (is_lambda(t)) {
            expr d = instantiate_rev(binding_domain(t), locals.size(), locals.data());
            locals.push_local(binding_name(t), d, binding_info(t));
            t = binding_body(t);
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);
        return locals.mk_lambda(t);
    }

    virtual expr visit_lambda(expr const & e) override {
        expr new_e = visit_lambda_core(e);
        idx2decls map;
        collect_locals(new_e, map);
        if (map.empty()) {
            return declare_aux_def(new_e);
        } else {
            buffer<expr> args;
            while (!map.empty()) {
                /* remove local_decl with biggest idx */
                local_decl d = map.erase_min();
                expr l       = d.mk_ref();
                if (auto v = d.get_value()) {
                    collect_locals(*v, map);
                    new_e = instantiate(abstract_local(new_e, l), *v);
                } else {
                    collect_locals(d.get_type(), map);
                    if (is_comp_irrelevant(ctx(), l))
                        args.push_back(mark_comp_irrelevant(l));
                    else
                        args.push_back(l);
                    new_e = abstract_local(new_e, l);
                    new_e = mk_lambda(d.get_name(), d.get_type(), new_e);
                }
            }
            expr c = declare_aux_def(new_e);
            return mk_rev_app(c, args);
        }
    }

    virtual expr visit_let(expr const & e) override {
        type_context::tmp_locals locals(m_ctx);
        expr t = e;
        while (is_let(t)) {
            expr d = instantiate_rev(let_type(t), locals.size(), locals.data());
            expr v = visit(instantiate_rev(let_value(t), locals.size(), locals.data()));
            locals.push_let(let_name(t), d, v);
            t = let_body(t);
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);
        return locals.mk_let(t);
    }

    virtual expr visit_app(expr const & e) override {
        // TODO(Leo): process recursor args
        return compiler_step_visitor::visit_app(e);
    }

public:
    lambda_lifting_fn(environment const & env, buffer<name> & new_decls, bool trusted):
        compiler_step_visitor(env), m_new_decls(new_decls), m_trusted(trusted) {}

    environment const & env() const { return m_env; }

    expr operator()(expr const & e) {
        if (is_lambda(e))
            return visit_lambda_core(e);
        else
            return visit(e);
    }
};

expr lambda_lifting(environment & env, expr const & e, buffer<name> & new_decls, bool trusted) {
    lambda_lifting_fn fn(env, new_decls, trusted);
    expr new_e = fn(e);
    env = fn.env();
    return new_e;
}
}

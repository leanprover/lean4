/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/normalize.h"
#include "library/util.h"
#include "library/trace.h"
#include "kernel/scope_pos_info_provider.h"
#include "library/module.h"
#include "library/vm/vm.h"
#include "library/sorry.h"
#include "library/compiler/util.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/procedure.h"

namespace lean {
class lambda_lifting_fn : public compiler_step_visitor {
    buffer<procedure> m_new_procs;
    name              m_prefix;
    unsigned          m_idx;
    bool              m_saw_sorry = false;

    optional<pos_info> get_pos_info(expr e) {
        pos_info_provider * pip = get_pos_info_provider();
        if (!pip) {
            /* Try position for main application */
            return get_decl_pos_info(m_ctx.env(), m_prefix);
        }
        while (is_lambda(e)) {
            if (auto r = pip->get_pos_info(e))
                return r;
            e = binding_body(e);
        }
        return get_decl_pos_info(m_ctx.env(), m_prefix);
    }

    typedef rb_map<unsigned, local_decl, unsigned_rev_cmp> idx2decls;

    void collect_locals(expr const & e, idx2decls & r) {
        local_context const & lctx = ctx().lctx();
        for_each(e, [&](expr const & e, unsigned) {
                if (is_local_decl_ref(e)) {
                    local_decl d = lctx.get_local_decl(e);
                    r.insert(d.get_idx(), d);
                }
                return true;
            });
    }

    expr visit_lambda_core(expr const & e) {
        type_context_old::tmp_locals locals(m_ctx);
        expr t = e;
        while (is_lambda(t)) {
            lean_assert(is_neutral_expr(binding_domain(t)) || closed(binding_domain(t)));
            locals.push_local(binding_name(t), binding_domain(t), binding_info(t));
            t = binding_body(t);
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);
        return copy_tag(e, locals.mk_lambda(t));
    }

    expr abstract_locals(expr e, buffer<expr> & locals) {
        idx2decls map;
        collect_locals(e, map);
        if (map.empty()) {
            return e;
        } else {
            while (!map.empty()) {
                /* Remove local_decl with biggest idx */
                local_decl d = map.erase_min();
                /* Remark: lambda lifting is applied after the erase_irrelevant step.
                   So, we don't need to make sure the result can be type checked by the Lean kernel.
                   Therefore, we don't need to be concerned about let-expressions when performing
                   lambda lifting. That is, we don't need to be concerned about
                   the case where

                      (let x := v in f[x]) is type correct, but
                      ((fun x, f [x]) v) isn't.

                   In the past, we would expand let-expressions to avoid this non-issue,
                   and it would create performance problems in the generated code.
                */
                expr l       = d.mk_ref();
                locals.push_back(l);
                e = abstract_local(e, l);
                e = mk_lambda(d.get_name(), d.get_type(), e);
            }
            return e;
        }
    }

    /* Auxiliary function for visit_lambda. It is used to avoid unnecessary aux decl by
       1- Apply eta-reduction (unless there is a sorry)
       2- Check if the result is of the form (f ...) where f is
         a) not VM builtin functions NOR
         b) A function without builtin support (i.e., it is not a constructor, cases_on or projection) */
    optional<expr> try_eta(expr const & value) {
        if (m_saw_sorry && has_sorry(value))
            return none_expr();

        expr new_value = ::lean::try_eta(value);
        expr const & fn = get_app_fn(new_value);

        if (is_local(fn))
            return some_expr(new_value);

        if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (!inductive::is_intro_rule(env(), n) && !is_cases_on_recursor(env(), n) && !is_projection(env(), n))
                return some_expr(new_value);
        }

        return none_expr();
    }

    virtual expr visit_lambda(expr const & e) override {
        expr new_e = visit_lambda_core(e);

        if (auto r = try_eta(new_e))
            return *r;

        buffer<expr> locals;
        new_e = abstract_locals(new_e, locals);
        name aux_name = mk_compiler_unused_name(env(), m_prefix, "_lambda", m_idx);
        m_new_procs.emplace_back(aux_name, get_pos_info(e), new_e);
        return mk_rev_app(mk_constant(aux_name), locals);
    }

    virtual expr visit_let(expr const & e) override {
        type_context_old::tmp_locals locals(m_ctx);
        expr t = e;
        while (is_let(t)) {
            lean_assert(is_neutral_expr(let_type(t)) || closed(let_type(t)));
            expr v = visit(instantiate_rev(let_value(t), locals.size(), locals.data()));
            locals.push_let(let_name(t), let_type(t), v);
            t = let_body(t);
        }
        t = instantiate_rev(t, locals.size(), locals.data());
        t = visit(t);
        return locals.mk_let(t);
    }

    expr visit_cases_on_minor(unsigned data_sz, expr e) {
        type_context_old::tmp_locals locals(ctx());
        for (unsigned i = 0; i < data_sz; i++) {
            if (is_lambda(e)) {
                expr l = locals.push_local_from_binding(e);
                e = instantiate(binding_body(e), l);
            } else {
                expr l = locals.push_local("a", mk_neutral_expr());
                e = mk_app(e, l);
            }
        }
        e = visit(e);
        return locals.mk_lambda(e);
    }

    /* We should preserve the lambda's in minor premises */
    expr visit_cases_on_app(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        name const & rec_name       = const_name(fn);
        name const & I_name         = rec_name.get_prefix();
        /* erase_irrelevant already removed parameters and indices from cases_on applications */
        unsigned nminors            = *inductive::get_num_minor_premises(env(), I_name);
        unsigned nparams            = *inductive::get_num_params(env(), I_name);
        unsigned arity              = nminors + 1 /* major premise */;
        unsigned major_idx          = 0;
        unsigned first_minor_idx    = 1;
        /* This transformation assumes eta-expansion have already been applied.
           So, we should have a sufficient number of arguments. */
        lean_assert(args.size() >= arity);
        buffer<name> cnames;
        get_intro_rule_names(env(), I_name, cnames);
        /* Process major premise */
        args[major_idx]        = visit(args[major_idx]);
        /* Process extra arguments */
        for (unsigned i = arity; i < args.size(); i++)
            args[i] = visit(args[i]);
        /* Process minor premises */
        for (unsigned i = 0, j = first_minor_idx; i < cnames.size(); i++, j++) {
            unsigned carity   = get_constructor_arity(env(), cnames[i]);
            lean_assert(carity >= nparams);
            unsigned cdata_sz = carity - nparams;
            args[j] = visit_cases_on_minor(cdata_sz, args[j]);
        }
        return mk_app(fn, args);
    }

    virtual expr visit_app(expr const & e) override {
        expr const & fn = get_app_fn(e);
        if (is_constant(fn) && is_cases_on_recursor(env(), const_name(fn))) {
            return visit_cases_on_app(e);
        } else {
            return compiler_step_visitor::visit_app(head_beta_reduce(e));
        }
    }

    virtual expr visit_macro(expr const & e) override {
        if (is_sorry(e)) m_saw_sorry = true;
        return compiler_step_visitor::visit_macro(e);
    }

public:
    lambda_lifting_fn(environment const & env, abstract_context_cache & cache, name const & prefix):
        compiler_step_visitor(env, cache), m_prefix(prefix), m_idx(1) {
    }

    void operator()(buffer<procedure> & procs) {
        for (auto p : procs) {
            expr val     = p.m_code;
            expr new_val = is_lambda(val) ? visit_lambda_core(val) : visit(val);
            m_new_procs.emplace_back(p.m_name, p.m_pos, new_val);
        }
        procs.clear();
        procs.append(m_new_procs);
    }
};

void lambda_lifting(environment const & env, abstract_context_cache & cache, name const & prefix, buffer<procedure> & procs) {
    return lambda_lifting_fn(env, cache, prefix)(procs);
}
}

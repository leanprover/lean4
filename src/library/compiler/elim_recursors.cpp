/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/inductive/inductive.h"
#include "library/locals.h"
#include "library/module.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/normalize.h"
#include "library/compiler/util.h"
#include "library/compiler/procedure.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/compiler_step_visitor.h"
#include "library/compiler/rec_fn_macro.h"

namespace lean {
class elim_recursors_fn : public compiler_step_visitor {
    name                m_prefix;
    unsigned            m_idx;
    buffer<procedure> & m_new_decls;
protected:
    expr declare_aux_def(name const & n, expr const & value) {
        m_new_decls.emplace_back(n, get_decl_pos_info(m_ctx.env(), m_prefix), value);
        /* We should use a new type checker because m_env is updated by this object.
           It is safe to use type_checker because value does not contain local_decl_ref objects. */
        level_param_names ps = to_level_param_names(collect_univ_params(value));
        type_checker tc(m_env);
        expr type         = tc.infer(value);
        bool trusted      = false;
        /* We add declaration as a constant to make sure
           we can infer the type of the resultant expression. */
        declaration new_decl = mk_constant_assumption(n, ps, type, trusted);
        m_env = m_env.add(check(m_env, new_decl));
        return mk_constant(n, param_names_to_levels(ps));
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

    expr abstract_locals(expr e, buffer<expr> & locals) {
        idx2decls map;
        collect_locals(e, map);
        if (map.empty()) {
            return e;
        } else {
            while (!map.empty()) {
                /* remove local_decl with biggest idx */
                local_decl d = map.erase_min();
                expr l       = d.mk_ref();
                if (auto v = d.get_value()) {
                    collect_locals(*v, map);
                    e = instantiate(abstract_local(e, l), *v);
                } else {
                    collect_locals(d.get_type(), map);
                    if (is_comp_irrelevant(ctx(), l))
                        locals.push_back(mark_comp_irrelevant(l));
                    else
                        locals.push_back(l);
                    e = abstract_local(e, l);
                    e = mk_lambda(d.get_name(), d.get_type(), e);
                }
            }
            return e;
        }
    }

    expr consume_lambdas(type_context_old::tmp_locals & locals, expr e) {
        while (true) {
            expr new_e = ctx().whnf(e);
            if (is_lambda(new_e)) {
                e = new_e;
                expr local = locals.push_local_from_binding(e);
                e = instantiate(binding_body(e), local);
            } else {
                return head_beta_reduce(e);
            }
        }
    }

    /* Process recursor application of recursive datatype.
       We create a auxiliary recursive definition using cases_on and rec_fn_macro. */
    expr visit_recursor_app(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        name const & rec_name     = const_name(fn);
        name const & I_name       = rec_name.get_prefix();
        unsigned nparams          = *inductive::get_num_params(env(), I_name);
        unsigned nminors          = *inductive::get_num_minor_premises(env(), I_name);
        unsigned nindices         = *inductive::get_num_indices(env(), I_name);
        unsigned first_minor_idx  = nparams + 1;
        /* Create auxiliary application containing params + typeformer + minor premises.
           This application is going to be the base of the auxiliary recursive definition. */
        expr aux = mk_app(fn, nparams + 1 + nminors, args.data());
        /* Abstract locals (and let values) occurring in aux */
        buffer<expr> abst_locals;
        aux = abstract_locals(aux, abst_locals);
        /* Create expr (rec_fn) for representing recursive calls. */
        expr aux_decl_type = ctx().infer(aux);
        name aux_decl_name = mk_compiler_unused_name(m_env, m_prefix, "_rec", m_idx);
        expr rec_fn = mk_rec_fn_macro(aux_decl_name, aux_decl_type);
        /* Create new locals for aux.
           The operating abstract_locals creates a lambda-abstraction around aux if it uses
           local constants. */
        type_context_old::tmp_locals locals(m_ctx);
        buffer<expr> aux_decl_params; /* "fixed" parameters of the auxiliary recursive declaration. */
        expr aux_body = aux;
        while (is_lambda(aux_body)) {
            expr d = instantiate_rev(binding_domain(aux_body), locals.size(), locals.data());
            expr p = locals.push_local(binding_name(aux_body), d, binding_info(aux_body));
            aux_decl_params.push_back(p);
            aux_body = binding_body(aux_body);
        }
        aux_body = instantiate_rev(aux_body, locals.size(), locals.data());
        lean_assert(is_app(aux_body) && is_constant(get_app_fn(aux_body), rec_name));
        buffer<expr> aux_body_args;
        get_app_args(aux_body, aux_body_args);
        /* Update rec_fn, create an application using aux_decl_params.
           These parameters are fixed in recursive calls. */
        rec_fn = mk_app(rec_fn, aux_decl_params);
        /* Create locals for indices and major premise */
        expr aux_body_type = ctx().infer(aux_body);
        buffer<expr> indices;
        for (unsigned i = 0; i < nindices; i++) {
            aux_body_type = ctx().whnf(aux_body_type);
            lean_assert(is_pi(aux_body_type));
            expr index = locals.push_local_from_binding(aux_body_type);
            indices.push_back(index);
            aux_body_type = instantiate(binding_body(aux_body_type), index);
        }
        aux_body_type = ctx().whnf(aux_body_type);
        lean_assert(is_pi(aux_body_type));
        expr major = locals.push_local_from_binding(aux_body_type);
        /* Make sure result is eta-expanded */
        buffer<expr> extra_args; /* to make sure result is eta-expanded */
        aux_body_type = instantiate(binding_body(aux_body_type), major);
        while (true) {
            aux_body_type = ctx().whnf(aux_body_type);
            if (!is_pi(aux_body_type))
                break;
            expr new_arg = locals.push_local_from_binding(aux_body_type);
            extra_args.push_back(new_arg);
            aux_body_type = instantiate(binding_body(aux_body_type), new_arg);
        }
        /* Create auxiliary recursive function. It is a cases_on expression. */
        buffer<expr> cases_on_args;
        {
            /* Add parameters and motive from aux_body_args */
            cases_on_args.append(nparams + 1, aux_body_args.data());
            /* Add indices */
            cases_on_args.append(indices);
            /* Add major */
            cases_on_args.push_back(major);
            /* Add minor premises */
            buffer<name> cnames; /* constructor names */
            get_intro_rule_names(env(), I_name, cnames);
            for (unsigned i = 0; i < nminors; i++) {
                // tout() << ">> cname: " << cnames[i] << "\n";
                unsigned carity = get_constructor_arity(env(), cnames[i]);
                expr minor      = aux_body_args[first_minor_idx + i];
                // tout() << ">> minor: " << minor << "\n";
                type_context_old::tmp_locals minor_locals(m_ctx);
                buffer<expr> minor_recs; /* "recursive calls" */
                lean_assert(carity >= nparams);
                buffer<bool> rec_mask;
                get_constructor_rec_arg_mask(env(), cnames[i], rec_mask);
                for (unsigned j = 0; j < carity - nparams; j++) {
                    minor            = ctx().whnf(minor);
                    lean_assert(is_lambda(minor));
                    expr minor_local = minor_locals.push_local_from_binding(minor);
                    minor = instantiate(binding_body(minor), minor_local);
                    /* Check if minor_local is recursive data */
                    type_context_old::tmp_locals aux_locals(m_ctx);
                    expr minor_local_type = ctx().whnf(ctx().infer(minor_local));
                    // tout() << ">>> minor_local_type: " << minor_local_type << "\n";
                    while (is_pi(minor_local_type)) {
                        expr aux_local = aux_locals.push_local_from_binding(minor_local_type);
                        minor_local_type = ctx().whnf(instantiate(binding_body(minor_local_type), aux_local));
                    }
                    if (rec_mask[nparams + j]) {
                        /* Recursive data, we must update minor_recs */
                        buffer<expr> I_args;
                        get_app_args(minor_local_type, I_args);
                        lean_assert(I_args.size() == nparams + nindices);
                        /* Construct term to replace the inductive/recursive hypothesis and add it to minor_recs.
                           The term is of the form
                              fun aux_locals, rec_fn I_args_indices (minor_local aux_locals)
                        */
                        expr rec_fn_indices = mk_app(rec_fn, nindices, I_args.data() + nparams);
                        expr minor_rec = mk_app(rec_fn_indices, mk_app(minor_local, aux_locals.as_buffer()));
                        minor_rec = aux_locals.mk_lambda(minor_rec);
                        // tout() << ">> minor_rec: " << minor_rec << "\n";
                        minor_recs.push_back(minor_rec);
                    }
                }
                /* Replace recursive/inductive hypothesis with minor_recs */
                for (expr const & minor_rec : minor_recs) {
                    minor = ctx().whnf(minor);
                    // tout() << ">> minor: " << minor << "\n";
                    lean_assert(is_lambda(minor));
                    minor = instantiate(binding_body(minor), minor_rec);
                }
                /* Keep consuming lambda */
                minor = consume_lambdas(minor_locals, minor);
                minor = visit(head_beta_reduce(minor));
                minor = minor_locals.mk_lambda(minor);
                cases_on_args.push_back(minor);
            }
        }
        name cases_on_name  = name(I_name, "cases_on");
        expr cases_on_fn    = mk_constant(cases_on_name, const_levels(fn));
        expr cases_on       = mk_app(mk_app(cases_on_fn, cases_on_args), extra_args);
        expr aux_decl_value = locals.mk_lambda(cases_on);
        expr aux_decl_cnst  = declare_aux_def(aux_decl_name, aux_decl_value);
        buffer<expr> rest_args;
        for (unsigned i = nparams + 1 + nminors; i < args.size(); i++)
            rest_args.push_back(visit(args[i]));
        expr r = mk_app(mk_rev_app(aux_decl_cnst, abst_locals), rest_args);
        return r;
    }

    bool is_recursive_recursor(name const & n) {
        if (auto I_name = inductive::is_elim_rule(env(), n)) {
            return is_recursive_datatype(env(), *I_name);
        }
        return false;
    }

    virtual expr visit_app(expr const & e) override {
        expr const & fn = get_app_fn(e);
        if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (inductive::is_elim_rule(env(), n) && is_recursive_recursor(n)) {
                return visit_recursor_app(e);
            }
        }
        return compiler_step_visitor::visit_app(head_beta_reduce(e));
    }

public:
    elim_recursors_fn(environment const & env, abstract_context_cache & cache,
                      name const & prefix, buffer<procedure> & new_decls):
        compiler_step_visitor(env, cache), m_prefix(prefix), m_idx(1), m_new_decls(new_decls) {}

    environment const & env() const { return m_env; }
};

expr elim_recursors(environment & env, abstract_context_cache & cache,
                    name const & prefix, expr const & e, buffer<procedure> & new_decls) {
    elim_recursors_fn fn(env, cache, prefix, new_decls);
    expr new_e = fn(e);
    env = fn.env();
    return new_e;
}
}

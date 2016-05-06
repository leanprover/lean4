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
#include "library/util.h"
#include "library/trace.h"
#include "library/normalize.h"
#include "compiler/fresh_constant.h"
#include "compiler/util.h"
#include "compiler/comp_irrelevant.h"
#include "compiler/compiler_step_visitor.h"
#include "compiler/rec_fn_macro.h"

namespace lean {
class lambda_lifting_fn : public compiler_step_visitor {
    buffer<name> & m_new_decls;
    bool           m_trusted;
protected:
    expr declare_aux_def_core(name const & n, expr const & value) {
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

    expr declare_aux_def(expr const & value) {
        expr new_value = try_eta(value);
        if (!is_lambda(new_value))
            return new_value;
        pair<environment, name> ep = mk_fresh_constant(m_env);
        m_env  = ep.first;
        name n = ep.second;
        return declare_aux_def_core(n, value);
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

    virtual expr visit_lambda(expr const & e) override {
        expr new_e = visit_lambda_core(e);
        buffer<expr> locals;
        new_e  = abstract_locals(new_e, locals);
        expr c = declare_aux_def(new_e);
        return mk_rev_app(c, locals);
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
        expr aux_decl_type = m_ctx.infer(aux);
        pair<environment, name> ep = mk_fresh_constant(m_env, "_rec");
        m_env = ep.first;
        name aux_decl_name = ep.second;
        expr rec_fn = mk_rec_fn_macro(aux_decl_name, aux_decl_type);
        /* Create new locals for aux.
           The operating abstract_locals creates a lambda-abstraction around aux if it uses
           local constants. */
        type_context::tmp_locals locals(m_ctx);
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
        expr aux_body_type = m_ctx.infer(aux_body);
        buffer<expr> indices;
        for (unsigned i = 0; i < nindices; i++) {
            aux_body_type = m_ctx.whnf(aux_body_type);
            lean_assert(is_pi(aux_body_type));
            expr index = locals.push_local(binding_name(aux_body_type), binding_domain(aux_body_type), binding_info(aux_body_type));
            indices.push_back(index);
            aux_body_type = instantiate(binding_body(aux_body_type), index);
        }
        aux_body_type = m_ctx.whnf(aux_body_type);
        lean_assert(is_pi(aux_body_type));
        expr major = locals.push_local(binding_name(aux_body_type), binding_domain(aux_body_type), binding_info(aux_body_type));
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
                unsigned carity = get_constructor_arity(cnames[i]);
                expr minor      = aux_body_args[first_minor_idx + i];
                // tout() << ">> minor: " << minor << "\n";
                type_context::tmp_locals minor_locals(m_ctx);
                buffer<expr> minor_recs; /* "recursive calls" */
                lean_assert(carity >= nparams);
                for (unsigned j = 0; j < carity - nparams; j++) {
                    minor            = ctx().whnf(minor);
                    lean_assert(is_lambda(minor));
                    expr minor_local = minor_locals.push_local(binding_name(minor), binding_domain(minor), binding_info(minor));
                    minor = instantiate(binding_body(minor), minor_local);
                    /* Check if minor_local is recursive data */
                    type_context::tmp_locals aux_locals(m_ctx);
                    expr minor_local_type = m_ctx.whnf(ctx().infer(minor_local));
                    // tout() << ">>> minor_local_type: " << minor_local_type << "\n";
                    while (is_pi(minor_local_type)) {
                        expr aux_local = aux_locals.push_local(binding_name(minor_local_type), binding_domain(minor_local_type), binding_info(minor_local_type));
                        minor_local_type = m_ctx.whnf(instantiate(binding_body(minor_local_type), aux_local));
                    }
                    if (is_constant(get_app_fn(minor_local_type), I_name)) {
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
                while (true) {
                    expr new_minor = ctx().whnf(minor);
                    if (is_lambda(new_minor)) {
                        minor = new_minor;
                        expr minor_local = minor_locals.push_local(binding_name(minor), binding_domain(minor), binding_info(minor));
                        minor = instantiate(binding_body(minor), minor_local);
                    } else {
                        break;
                    }
                }
                minor = visit(minor);
                minor = minor_locals.mk_lambda(minor);
                cases_on_args.push_back(minor);
            }
        }
        name cases_on_name  = name(I_name, "cases_on");
        expr cases_on_fn    = mk_constant(cases_on_name, const_levels(fn));
        expr cases_on       = mk_app(cases_on_fn, cases_on_args);
        expr aux_decl_value = locals.mk_lambda(cases_on);
        expr aux_decl_cnst  = declare_aux_def_core(aux_decl_name, aux_decl_value);
        unsigned num_rest_args = args.size() - nparams - 1 - nminors;
        expr const * rest_args = args.data() + nparams + 1 + nminors;
        expr r = mk_app(mk_app(aux_decl_cnst, abst_locals), num_rest_args, rest_args);
        return r;
    }

    bool is_nonrecursive_recursor(name const & n) {
        if (auto I_name = inductive::is_elim_rule(env(), n)) {
            return !is_recursive_datatype(env(), *I_name);
        }
        return false;
    }

    unsigned get_constructor_arity(name const & n) {
        declaration d = env().get(n);
        expr e = d.get_type();
        unsigned r = 0;
        while (is_pi(e)) {
            r++;
            e = binding_body(e);
        }
        return r;
    }

    expr visit_cases_on_minor(unsigned data_sz, expr e) {
        type_context::tmp_locals locals(ctx());
        for (unsigned i = 0; i < data_sz; i++) {
            e = ctx().whnf(e);
            lean_assert(is_lambda(e));
            expr l = locals.push_local(binding_name(e), binding_domain(e), binding_info(e));
            e = instantiate(binding_body(e), l);
        }
        e = beta_reduce(e);
        e = visit(e);
        return locals.mk_lambda(e);
    }

    /** Process C.cases_on applications and C.rec application for non-recursive C */
    expr visit_cases_on_app(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        bool is_cases_on            = is_cases_on_recursor(env(), const_name(fn));
        name const & rec_name       = const_name(fn);
        name const & I_name         = rec_name.get_prefix();
        unsigned nparams            = *inductive::get_num_params(env(), I_name);
        unsigned nminors            = *inductive::get_num_minor_premises(env(), I_name);
        unsigned nindices           = *inductive::get_num_indices(env(), I_name);
        unsigned arity              = nparams + 1 /* typeformer/motive */ + nindices + 1 /* major premise */ + nminors;
        unsigned major_idx;
        unsigned first_minor_idx;
        if (is_cases_on) {
            major_idx       = nparams + 1 + nindices;
            first_minor_idx = major_idx + 1;
        } else {
            major_idx       = *inductive::get_elim_major_idx(env(), rec_name);
            first_minor_idx = nparams + 1;
        }
        /* This transformation assumes eta-expansion have already been applied.
           So, we should have a sufficient number of arguments. */
        lean_assert(args.size() >= arity);
        buffer<name> cnames;
        get_intro_rule_names(env(), I_name, cnames);
        /* Process major premise */
        args[major_idx]        = visit(args[major_idx]);
        if (is_constructor_app(env(), args[major_idx])) {
            /* Major premise became a constructor. So, we should reduce. */
            expr new_e = mk_app(fn, args);
            if (auto r = ctx().norm_ext(new_e))
                return compiler_step_visitor::visit(beta_reduce(*r));
        }
        /* Process extra arguments */
        for (unsigned i = arity; i < args.size(); i++)
            args[i] = visit(args[i]);
        /* Process minor premises */
        for (unsigned i = 0, j = first_minor_idx; i < cnames.size(); i++, j++) {
            unsigned carity   = get_constructor_arity(cnames[i]);
            lean_assert(carity >= nparams);
            unsigned cdata_sz = carity - nparams;
            args[j] = visit_cases_on_minor(cdata_sz, args[j]);
        }
        return mk_app(fn, args);
    }

    virtual expr visit_app(expr const & e) override {
        expr const & fn = get_app_fn(e);
        if (is_constant(fn)) {
            name const & n = const_name(fn);
            if (is_cases_on_recursor(env(), n) || is_nonrecursive_recursor(n)) {
                return visit_cases_on_app(e);
            } else if (inductive::is_elim_rule(env(), n)) {
                return visit_recursor_app(e);
            }
        }
        return compiler_step_visitor::visit_app(beta_reduce(e));
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

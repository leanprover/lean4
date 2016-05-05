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

namespace lean {
class lambda_lifting_fn : public compiler_step_visitor {
    buffer<name> & m_new_decls;
    bool           m_trusted;
protected:
    expr declare_aux_def(expr const & value) {
        expr new_value = try_eta(value);
        if (!is_lambda(new_value))
            return new_value;
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

    expr visit_recursor_app(expr const & e) {
        // TODO(Leo): process recursor args
        return compiler_step_visitor::visit_app(e);
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

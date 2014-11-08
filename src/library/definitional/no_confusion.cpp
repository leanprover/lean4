/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "kernel/type_checker.h"
#include "library/protected.h"
#include "library/module.h"

namespace lean {
static void throw_corrupted(name const & n) {
    throw exception(sstream() << "error in 'no_confusion' generation, '" << n << "' inductive datatype declaration is corrupted");
}

environment mk_no_confusion_type(environment const & env, name const & n) {
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        throw exception(sstream() << "error in 'no_confusion' generation, '" << n << "' is not an inductive datatype");
    name_generator ngen;
    unsigned nparams       = std::get<1>(*decls);
    declaration ind_decl   = env.get(n);
    declaration cases_decl = env.get(name(n, "cases_on"));
    level_param_names lps  = cases_decl.get_univ_params();
    level  rlvl            = mk_param_univ(head(lps));
    levels ilvls           = param_names_to_levels(tail(lps));
    if (length(ilvls) != length(ind_decl.get_univ_params()))
        return env; // type is a proposition
    expr ind_type          = instantiate_type_univ_params(ind_decl, ilvls);
    name eq_name("eq");
    name heq_name("heq");
    name eq_refl_name{"eq", "refl"};
    name heq_refl_name{"heq", "refl"};
    // All inductive datatype parameters and indices are arguments
    buffer<expr> args;
    while (is_pi(ind_type)) {
        expr arg = mk_local(ngen.next(), binding_name(ind_type), binding_domain(ind_type), mk_implicit_binder_info());
        args.push_back(arg);
        ind_type = instantiate(binding_body(ind_type), arg);
    }
    if (!is_sort(ind_type) || args.size() < nparams)
        throw_corrupted(n);
    if (env.impredicative() && is_zero(sort_level(ind_type)))
        return env; // do nothing, inductive type is a proposition
    unsigned nindices      = args.size() - nparams;
    // Create inductive datatype
    expr I = mk_app(mk_constant(n, ilvls), args);
    // Add (P : Type)
    expr P = mk_local(ngen.next(), "P", mk_sort(rlvl), binder_info());
    args.push_back(P);
    // add v1 and v2 elements of the inductive type
    expr v1 = mk_local(ngen.next(), "v1", I, binder_info());
    expr v2 = mk_local(ngen.next(), "v2", I, binder_info());
    args.push_back(v1);
    args.push_back(v2);
    expr R  = mk_sort(rlvl);
    name no_confusion_type_name{n, "no_confusion_type"};
    expr no_confusion_type_type = Pi(args, R);
    // Create type former
    buffer<expr> type_former_args;
    for (unsigned i = nparams; i < nparams + nindices; i++)
        type_former_args.push_back(args[i]);
    type_former_args.push_back(v1);
    expr type_former = Fun(type_former_args, R);
    // Create cases_on
    levels clvls   = levels(mk_succ(rlvl), ilvls);
    expr cases_on  = mk_app(mk_app(mk_constant(cases_decl.get_name(), clvls), nparams, args.data()), type_former);
    cases_on       = mk_app(cases_on, nindices, args.data() + nparams);
    expr cases_on1 = mk_app(cases_on, v1);
    expr cases_on2 = mk_app(cases_on, v2);
    type_checker tc(env);
    expr t1        = tc.infer(cases_on1).first;
    expr t2        = tc.infer(cases_on2).first;
    buffer<expr> outer_cases_on_args;
    unsigned idx1 = 0;
    while (is_pi(t1)) {
        expr minor1 = tc.whnf(binding_domain(t1)).first;
        buffer<expr> minor1_args;
        while (is_pi(minor1)) {
            expr arg = mk_local(ngen.next(), binding_name(minor1), binding_domain(minor1), binding_info(minor1));
            minor1_args.push_back(arg);
            minor1   = tc.whnf(instantiate(binding_body(minor1), arg)).first;
        }
        expr curr_t2  = t2;
        buffer<expr> inner_cases_on_args;
        unsigned idx2 = 0;
        while (is_pi(curr_t2)) {
            expr minor2 = tc.whnf(binding_domain(curr_t2)).first;
            buffer<expr> minor2_args;
            while (is_pi(minor2)) {
                expr arg = mk_local(ngen.next(), binding_name(minor2), binding_domain(minor2), binding_info(minor2));
                minor2_args.push_back(arg);
                minor2   = tc.whnf(instantiate(binding_body(minor2), arg)).first;
            }
            if (idx1 != idx2) {
                // infeasible case, constructors do not match
                inner_cases_on_args.push_back(Fun(minor2_args, P));
            } else {
                if (minor1_args.size() != minor2_args.size())
                    throw_corrupted(n);
                buffer<expr> rtype_hyp;
                // add equalities
                for (unsigned i = 0; i < minor1_args.size(); i++) {
                    expr lhs      = minor1_args[i];
                    expr rhs      = minor2_args[i];
                    expr lhs_type = mlocal_type(lhs);
                    expr rhs_type = mlocal_type(rhs);
                    level l       = sort_level(tc.ensure_type(lhs_type).first);
                    expr h_type;
                    if (tc.is_def_eq(lhs_type, rhs_type).first) {
                        h_type = mk_app(mk_constant(eq_name, to_list(l)), lhs_type, lhs, rhs);
                    } else {
                        h_type = mk_app(mk_constant(heq_name, to_list(l)), lhs_type, lhs, rhs_type, rhs);
                    }
                    rtype_hyp.push_back(mk_local(ngen.next(), local_pp_name(lhs).append_after("_eq"), h_type, binder_info()));
                }
                inner_cases_on_args.push_back(Fun(minor2_args, mk_arrow(Pi(rtype_hyp, P), P)));
            }
            idx2++;
            curr_t2 = binding_body(curr_t2);
        }
        outer_cases_on_args.push_back(Fun(minor1_args, mk_app(cases_on2, inner_cases_on_args)));
        idx1++;
        t1 = binding_body(t1);
    }
    expr no_confusion_type_value = Fun(args, mk_app(cases_on1, outer_cases_on_args));

    bool opaque       = false;
    bool use_conv_opt = true;
    declaration new_d = mk_definition(env, no_confusion_type_name, lps, no_confusion_type_type, no_confusion_type_value,
                                      opaque, ind_decl.get_module_idx(), use_conv_opt);
    environment new_env = module::add(env, check(env, new_d));
    return add_protected(new_env, no_confusion_type_name);
}

environment mk_no_confusion(environment const & env, name const & n) {
    return mk_no_confusion_type(env, n);
}
}

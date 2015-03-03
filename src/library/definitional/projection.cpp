/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"
#include "kernel/inductive/inductive.h"
#include "library/reducible.h"
#include "library/projection.h"
#include "library/module.h"
#include "library/util.h"
#include "library/normalize.h"
#include "library/definitional/projection.h"

namespace lean {
/** \brief Return true iff the type named \c S can be viewed as
    a structure in the given environment.

    If not, generate an error message using \c pos.
*/
bool is_structure(environment const & env, name const & S) {
    optional<inductive::inductive_decls> idecls = inductive::is_inductive_decl(env, S);
    if (!idecls || length(std::get<2>(*idecls)) != 1)
        return false;
    inductive::inductive_decl decl   = head(std::get<2>(*idecls));
    return length(inductive::inductive_decl_intros(decl)) == 1 && *inductive::get_num_indices(env, S) == 0;
}

[[ noreturn ]] static void throw_ill_formed(name const & n) {
    throw exception(sstream() << "projection generation, '" << n << "' is an ill-formed inductive datatype");
}

static pair<unsigned, inductive::intro_rule> get_nparam_intro_rule(environment const & env, name const & n) {
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        throw exception(sstream() << "projection generation, '" << n << "' is not an inductive datatype");
    optional<unsigned> num_indices = inductive::get_num_indices(env, n);
    if (num_indices && *num_indices > 0)
        throw exception(sstream() << "projection generation, '"
                        << n << "' is an indexed inductive datatype family");
    unsigned num_params = std::get<1>(*decls);
    for (auto const & decl : std::get<2>(*decls)) {
        if (inductive::inductive_decl_name(decl) == n) {
            auto intros = inductive::inductive_decl_intros(decl);
            if (length(intros) != 1)
                throw exception(sstream() << "projection generation, '"
                                << n << "' does not have a single constructor");
            return mk_pair(num_params, head(intros));
        }
    }
    throw_ill_formed(n);
}

static bool is_prop(expr type) {
    while (is_pi(type)) {
        type = binding_body(type);
    }
    return is_sort(type) && is_zero(sort_level(type));
}

environment mk_projections(environment const & env, name const & n, buffer<name> const & proj_names,
                           implicit_infer_kind infer_k, bool inst_implicit) {
    // Given an inductive datatype C A (where A represent parameters)
    //   intro : Pi A (x_1 : B_1[A]) (x_2 : B_2[A, x_1]) ..., C A
    //
    // we generate projections of the form
    //   proj_i A (c : C A) : B_i[A, (proj_1 A n), ..., (proj_{i-1} A n)]
    //     C.rec A (fun (x : C A), B_i[A, ...]) (fun (x_1 ... x_n), x_i) c
    auto p = get_nparam_intro_rule(env, n);
    name_generator ngen;
    unsigned nparams             = p.first;
    inductive::intro_rule intro  = p.second;
    expr intro_type              = inductive::intro_rule_type(intro);
    name rec_name                = inductive::get_elim_name(n);
    declaration ind_decl         = env.get(n);
    if (env.impredicative() && is_prop(ind_decl.get_type()))
        throw exception(sstream() << "projection generation, '" << n << "' is a proposition");
    declaration rec_decl         = env.get(rec_name);
    level_param_names lvl_params = ind_decl.get_univ_params();
    levels lvls                  = param_names_to_levels(lvl_params);
    buffer<expr> params; // datatype parameters
    for (unsigned i = 0; i < nparams; i++) {
        if (!is_pi(intro_type))
            throw_ill_formed(n);
        expr param = mk_local(ngen.next(), binding_name(intro_type), binding_domain(intro_type), binder_info());
        intro_type = instantiate(binding_body(intro_type), param);
        params.push_back(param);
    }
    expr C_A                     = mk_app(mk_constant(n, lvls), params);
    binder_info c_bi             = inst_implicit ? mk_inst_implicit_binder_info() : binder_info();
    expr c                       = mk_local(ngen.next(), name("c"), C_A, c_bi);
    buffer<expr> intro_type_args; // arguments that are not parameters
    expr it = intro_type;
    while (is_pi(it)) {
        expr local = mk_local(ngen.next(), binding_name(it), binding_domain(it), binding_info(it));
        intro_type_args.push_back(local);
        it = instantiate(binding_body(it), local);
    }
    buffer<expr> projs; // projections generated so far
    unsigned i = 0;
    environment new_env = env;
    for (name const & proj_name : proj_names) {
        if (!is_pi(intro_type))
            throw exception(sstream() << "generating projection '" << proj_name << "', '"
                            << n << "' does not have sufficient data");
        expr result_type   = binding_domain(intro_type);
        buffer<expr> proj_args;
        proj_args.append(params);
        proj_args.push_back(c);
        expr type_former   = Fun(c, result_type);
        expr minor_premise = Fun(intro_type_args, mk_var(intro_type_args.size() - i - 1));
        expr major_premise = c;
        type_checker tc(new_env);
        level l            = sort_level(tc.ensure_sort(tc.infer(result_type).first).first);
        levels rec_lvls    = append(to_list(l), lvls);
        expr rec           = mk_constant(rec_name, rec_lvls);
        buffer<expr> rec_args;
        rec_args.append(params);
        rec_args.push_back(type_former);
        rec_args.push_back(minor_premise);
        rec_args.push_back(major_premise);
        expr rec_app      = mk_app(rec, rec_args);
        expr proj_type    = Pi(proj_args, result_type);
        proj_type         = infer_implicit_params(proj_type, nparams, infer_k);
        expr proj_val     = Fun(proj_args, rec_app);
        bool opaque       = false;
        bool use_conv_opt = false;
        declaration new_d = mk_definition(env, proj_name, lvl_params, proj_type, proj_val,
                                          opaque, rec_decl.get_module_idx(), use_conv_opt);
        new_env = module::add(new_env, check(new_env, new_d));
        new_env = set_reducible(new_env, proj_name, reducible_status::Reducible);
        new_env = add_unfold_c_hint(new_env, proj_name, nparams);
        new_env = save_projection_info(new_env, proj_name, inductive::intro_rule_name(intro), nparams, i, inst_implicit);
        expr proj         = mk_app(mk_app(mk_constant(proj_name, lvls), params), c);
        intro_type        = instantiate(binding_body(intro_type), proj);
        i++;
    }
    return new_env;
}

static name mk_fresh_name(environment const & env, buffer<name> const & names, name const & s) {
    unsigned i = 1;
    name c = s;
    while (true) {
        if (!env.find(c) &&
            std::find(names.begin(), names.end(), c) == names.end())
            return c;
        c = s.append_after(i);
        i++;
    }
}

environment mk_projections(environment const & env, name const & n,
                           implicit_infer_kind infer_k, bool inst_implicit) {
    auto p  = get_nparam_intro_rule(env, n);
    unsigned num_params = p.first;
    inductive::intro_rule ir = p.second;
    expr type = inductive::intro_rule_type(ir);
    buffer<name> proj_names;
    unsigned i = 0;
    while (is_pi(type)) {
        if (i >= num_params)
            proj_names.push_back(mk_fresh_name(env, proj_names, n + binding_name(type)));
        i++;
        type = binding_body(type);
    }
    return mk_projections(env, n, proj_names, infer_k, inst_implicit);
}
}

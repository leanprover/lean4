/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "util/fresh_name.h"
#include "kernel/abstract.h"
#include "kernel/old_type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/kernel_exception.h"
#include "kernel/inductive/inductive.h"
#include "library/reducible.h"
#include "library/projection.h"
#include "library/module.h"
#include "library/util.h"
#include "library/normalize.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/class.h"
#include "library/constructions/projection.h"
#include "library/constructions/util.h"

namespace lean {
[[ noreturn ]] static void throw_ill_formed(name const & n) {
    throw exception(sstream() << "projection generation, '" << n << "' is an ill-formed inductive datatype");
}

static pair<unsigned, inductive::intro_rule> get_nparam_intro_rule(environment const & env, name const & n) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl)
        throw exception(sstream() << "projection generation, '" << n << "' is not an inductive datatype");
    optional<unsigned> num_indices = inductive::get_num_indices(env, n);
    if (num_indices && *num_indices > 0)
        throw exception(sstream() << "projection generation, '"
                        << n << "' is an indexed inductive datatype family");
    unsigned num_params = decl->m_num_params;
    auto intros = decl->m_intro_rules;
    if (length(intros) != 1)
        throw exception(sstream() << "projection generation, '"
                        << n << "' does not have a single constructor");
    return mk_pair(num_params, head(intros));
}

static bool is_prop(expr type) {
    while (is_pi(type)) {
        type = binding_body(type);
    }
    return is_sort(type) && is_zero(sort_level(type));
}


void initialize_def_projection() {
}

void finalize_def_projection() {
}

environment mk_projections(environment const & env, name const & n, buffer<name> const & proj_names,
                           buffer<implicit_infer_kind> const & infer_kinds, bool inst_implicit) {
    lean_assert(proj_names.size() == infer_kinds.size());
    name_generator ngen = mk_constructions_name_generator();
    auto p = get_nparam_intro_rule(env, n);
    unsigned nparams             = p.first;
    inductive::intro_rule intro  = p.second;
    expr intro_type              = inductive::intro_rule_type(intro);
    name rec_name                = inductive::get_elim_name(n);
    declaration ind_decl         = env.get(n);
    declaration rec_decl         = env.get(rec_name);
    bool is_predicate            = is_prop(ind_decl.get_type());
    level_param_names lvl_params = ind_decl.get_univ_params();
    levels lvls                  = param_names_to_levels(lvl_params);
    buffer<expr> params; // datatype parameters
    for (unsigned i = 0; i < nparams; i++) {
        if (!is_pi(intro_type))
            throw_ill_formed(n);
        auto bi = binding_info(intro_type);
        auto type = binding_domain(intro_type);
        if (!is_inst_implicit(bi))
            // We reset implicit binders in favor of having them inferred by `infer_implicit_params` later
            bi = mk_binder_info();
        if (is_class_out_param(type)) {
            // hide `out_param`
            type = app_arg(type);
            // out_params should always be implicit since they can be inferred from the later `c` argument
            bi = mk_implicit_binder_info();
        }
        expr param = mk_local(ngen.next(), binding_name(intro_type), type, bi);
        intro_type = instantiate(binding_body(intro_type), param);
        params.push_back(param);
    }
    expr C_A                     = mk_app(mk_constant(n, lvls), params);
    binder_info c_bi             = inst_implicit ? mk_inst_implicit_binder_info() : mk_binder_info();
    expr c                       = mk_local(ngen.next(), name("c"), C_A, c_bi);
    buffer<expr> intro_type_args; // arguments that are not parameters
    expr it = intro_type;
    while (is_pi(it)) {
        expr local = mk_local(ngen.next(), binding_name(it), binding_domain(it), binding_info(it));
        intro_type_args.push_back(local);
        it = instantiate(binding_body(it), local);
    }
    unsigned i = 0;
    environment new_env = env;
    for (name const & proj_name : proj_names) {
        if (!is_pi(intro_type))
            throw exception(sstream() << "generating projection '" << proj_name << "', '"
                            << n << "' does not have sufficient data");
        old_type_checker tc(new_env);
        expr result_type   = binding_domain(intro_type);
        if (is_predicate && !tc.is_prop(result_type)) {
            throw exception(sstream() << "failed to generate projection '" << proj_name << "' for '" << n << "', "
                            << "type is an inductive predicate, but field is not a proposition");
        }
        buffer<expr> proj_args;
        proj_args.append(params);
        proj_args.push_back(c);
        expr proj_type = Pi(proj_args, result_type);
        proj_type      = infer_implicit_params(proj_type, nparams, infer_kinds[i]);
        expr proj_val  = mk_proj(i, c);
        proj_val = Fun(proj_args, proj_val);
        declaration new_d = mk_definition_inferring_meta(env, proj_name, lvl_params, proj_type, proj_val,
                                                         reducibility_hints::mk_abbreviation());
        new_env = module::add(new_env, check(new_env, new_d));
        new_env = set_reducible(new_env, proj_name, reducible_status::Reducible, true);
        new_env = save_projection_info(new_env, proj_name, inductive::intro_rule_name(intro), nparams, i, inst_implicit);
        expr proj         = mk_app(mk_app(mk_constant(proj_name, lvls), params), c);
        intro_type        = instantiate(binding_body(intro_type), proj);
        i++;
    }
    return new_env;
}
}

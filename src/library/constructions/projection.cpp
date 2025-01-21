/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive.h"
#include "kernel/instantiate.h"
#include "library/reducible.h"
#include "library/projection.h"
#include "library/util.h"
#include "library/class.h"
#include "library/constructions/projection.h"
#include "library/constructions/util.h"

namespace lean {
[[ noreturn ]] static void throw_ill_formed(name const & n) {
    throw exception(sstream() << "projection generation, '" << n << "' is an ill-formed inductive datatype");
}

static bool is_prop(expr type) {
    while (is_pi(type)) {
        type = binding_body(type);
    }
    return is_sort(type) && is_zero(sort_level(type));
}

elab_environment mk_projections(elab_environment const & env, name const & n, buffer<name> const & proj_names, bool inst_implicit) {
    local_ctx lctx;
    name_generator ngen = mk_constructions_name_generator();
    constant_info ind_info       = env.get(n);
    if (!ind_info.is_inductive())
        throw exception(sstream() << "projection generation, '" << n << "' is not an inductive datatype");
    inductive_val ind_val        = ind_info.to_inductive_val();
    unsigned nparams             = ind_val.get_nparams();
    name rec_name                = mk_rec_name(n);
    if (ind_val.get_nindices() > 0)
        throw exception(sstream() << "projection generation, '" << n << "' is an indexed inductive datatype family");
    if (length(ind_val.get_cnstrs()) != 1)
        throw exception(sstream() << "projection generation, '" << n << "' does not have a single constructor");
    constant_info cnstr_info     = env.get(head(ind_val.get_cnstrs()));
    expr cnstr_type              = cnstr_info.get_type();
    bool is_predicate            = is_prop(ind_info.get_type());
    names lvl_params             = ind_info.get_lparams();
    levels lvls                  = lparams_to_levels(lvl_params);
    buffer<expr> params; // datatype parameters
    expr cnstr_type_orig = cnstr_type;
    for (unsigned i = 0; i < nparams; i++) {
        if (!is_pi(cnstr_type))
            throw_ill_formed(n);
        lean_assert(is_pi(cnstr_type_orig));
        auto bi = binding_info(cnstr_type);
        auto bi_orig = binding_info(cnstr_type_orig);
        auto type = binding_domain(cnstr_type);
        auto type_orig = binding_domain(cnstr_type_orig);
        if (!is_inst_implicit(bi_orig) && !is_class_out_param(type_orig)) {
            // We reset implicit binders in favor of having them inferred by `infer_implicit_params` later IF
            // 1. The original binder before `mk_outparam_args_implicit` is not an instance implicit.
            // 2. It is not originally an outparam. Outparams must be implicit.
            bi = mk_binder_info();
        } else if (is_inst_implicit(bi_orig) && inst_implicit) {
            bi = mk_implicit_binder_info();
        }
        expr param = lctx.mk_local_decl(ngen, binding_name(cnstr_type), type, bi);
        cnstr_type = instantiate(binding_body(cnstr_type), param);
        cnstr_type_orig = binding_body(cnstr_type_orig);
        params.push_back(param);
    }
    expr C_A                     = mk_app(mk_constant(n, lvls), params);
    binder_info c_bi             = inst_implicit ? mk_inst_implicit_binder_info() : mk_binder_info();
    expr c                       = lctx.mk_local_decl(ngen, name("self"), C_A, c_bi);
    buffer<expr> cnstr_type_args; // arguments that are not parameters
    expr it = cnstr_type;
    while (is_pi(it)) {
        expr local = lctx.mk_local_decl(ngen, binding_name(it), binding_domain(it), binding_info(it));
        cnstr_type_args.push_back(local);
        it = instantiate(binding_body(it), local);
    }
    unsigned i = 0;
    elab_environment new_env = env;
    for (name const & proj_name : proj_names) {
        if (!is_pi(cnstr_type))
            throw exception(sstream() << "generating projection '" << proj_name << "', '"
                            << n << "' does not have sufficient data");
        expr result_type   = consume_type_annotations(binding_domain(cnstr_type));
        bool is_prop       = type_checker(new_env, lctx).is_prop(result_type);
        if (is_predicate && !is_prop) {
            throw exception(sstream() << "failed to generate projection '" << proj_name << "' for '" << n << "', "
                            << "type is an inductive predicate, but field is not a proposition");
        }
        buffer<expr> proj_args;
        proj_args.append(params);
        proj_args.push_back(c);
        expr proj_type = lctx.mk_pi(proj_args, result_type);
        proj_type      = infer_implicit_params(proj_type, nparams, implicit_infer_kind::RelaxedImplicit);
        expr proj_val  = mk_proj(n, i, c);
        proj_val = lctx.mk_lambda(proj_args, proj_val);
        declaration new_d;
        if (is_prop) {
            bool unsafe = use_unsafe(env, proj_type) || use_unsafe(env, proj_val);
            if (unsafe) {
                // theorems cannot be unsafe
                new_d = mk_opaque(proj_name, lvl_params, proj_type, proj_val, unsafe);
            } else {
                new_d = mk_theorem(proj_name, lvl_params, proj_type, proj_val);
            }
        } else {
            new_d = mk_definition_inferring_unsafe(env, proj_name, lvl_params, proj_type, proj_val,
                                                           reducibility_hints::mk_abbreviation());
        }
        new_env = new_env.add(new_d);
        if (!inst_implicit && !is_prop)
            new_env = set_reducible(new_env, proj_name, reducible_status::Reducible, true);
        new_env = save_projection_info(new_env, proj_name, cnstr_info.get_name(), nparams, i, inst_implicit);
        expr proj    = mk_app(mk_app(mk_constant(proj_name, lvls), params), c);
        cnstr_type   = instantiate(binding_body(cnstr_type), proj);
        i++;
    }
    return new_env;
}


extern "C" LEAN_EXPORT object * lean_mk_projections(object * env, object * struct_name, object * proj_infos, uint8 inst_implicit) {
    elab_environment new_env(env);
    name n(struct_name);
    list_ref<name> ps(proj_infos);
    buffer<name> proj_names;
    for (auto p : ps) {
        proj_names.push_back(p);
    }
    return catch_kernel_exceptions<elab_environment>([&]() { return mk_projections(new_env, n, proj_names, inst_implicit != 0); });
}

void initialize_def_projection() {
}

void finalize_def_projection() {
}
}

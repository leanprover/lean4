/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/reducible.h"
#include "library/aux_recursors.h"

namespace lean {
static expr mk_local_from_binding(expr const & b) {
    lean_assert(is_binding(b));
    return mk_local(mk_fresh_name(), binding_name(b), binding_domain(b), binding_info(b));
}

environment mk_drec(environment const & env, name const & n) {
    if (!is_inductive_predicate(env, n))
        throw exception(sstream() << "error in 'drec' generation, '" << n << "' is not an inductive predicate");
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    type_checker tc(env);
    name rec_name          = inductive::get_elim_name(n);
    declaration rec_decl   = env.get(rec_name);
    declaration ind_decl   = env.get(n);
    unsigned num_idx_major = *inductive::get_num_indices(env, n) + 1;
    unsigned num_minors    = *inductive::get_num_minor_premises(env, n);
    unsigned major_idx     = *inductive::get_elim_major_idx(env, rec_name);
    unsigned num_params    = decl->m_num_params;
    levels lvls            = param_names_to_levels(rec_decl.get_univ_params());
    bool elim_to_prop      = rec_decl.get_num_univ_params() == ind_decl.get_num_univ_params();
    level elim_univ        = elim_to_prop ? mk_level_zero() : head(lvls);
    levels I_lvls          = elim_to_prop ? lvls : tail(lvls);
    buffer<expr> rec_params;
    expr rec_type = rec_decl.get_type();
    while (is_pi(rec_type)) {
        expr local = mk_local_from_binding(rec_type);
        rec_type   = instantiate(binding_body(rec_type), local);
        rec_params.push_back(local);
    }

    buffer<expr> drec_params;
    expr rec_cnst = mk_constant(rec_name, lvls);
    buffer<expr> rec_args; // arguments for rec used to define drec

    // Add params: As
    for (unsigned i = 0; i < num_params; i++) {
        drec_params.push_back(rec_params[i]);
        rec_args.push_back(rec_params[i]);
    }

    // Construct motive
    expr rec_motive = rec_params[num_params];
    name C_name     = mlocal_name(rec_motive);
    expr rec_motive_type = mlocal_type(rec_motive);
    buffer<expr> motive_params;
    while (is_pi(rec_motive_type)) {
        expr local = mk_local_from_binding(rec_motive_type);
        rec_motive_type = instantiate(binding_body(rec_motive_type), local);
        motive_params.push_back(local);
    }
    expr new_param_type  = mk_app(mk_app(mk_constant(n, I_lvls), num_params, rec_params.data()), motive_params);
    expr new_param       = mk_local(mk_fresh_name(), "h", new_param_type, binder_info());
    expr new_motive_type = Pi(motive_params, Pi(new_param, rec_motive_type));
    expr new_motive      = update_mlocal(rec_motive, new_motive_type);
    expr motive_arg      = Fun(motive_params, Pi(new_param, mk_app(mk_app(new_motive, motive_params), new_param)));
    drec_params.push_back(new_motive);
    rec_args.push_back(motive_arg);

    // Add minor premises to rec_params and rec_args
    unsigned i = num_params + 1;
    for (auto ir : decl->m_intro_rules) {
        name const & ir_name = inductive::intro_rule_name(ir);
        buffer<bool> rec_mask;
        get_constructor_rec_arg_mask(env, ir_name, rec_mask);
        unsigned num_fields = rec_mask.size() - num_params;
        expr const & minor  = rec_params[i];
        expr minor_type     = mlocal_type(minor);
        buffer<expr> new_minor_params;
        buffer<expr> recursive_params;
        buffer<expr> app_params;
        buffer<expr> app_args;
        unsigned j = 0;
        while (is_pi(minor_type)) {
            expr local      = mk_local_from_binding(minor_type);
            if (j < num_fields && rec_mask[num_params+j]) {
                recursive_params.push_back(local);
            }
            if (j < num_fields) {
                new_minor_params.push_back(local);
                app_params.push_back(local);
                app_args.push_back(local);
            } else {
                // inductive hypothesis
                lean_assert(j - num_fields < recursive_params.size());
                expr const & recursive_param = recursive_params[j - num_fields];
                expr ih_type = mlocal_type(local);
                buffer<expr> ih_params;
                while (is_pi(ih_type)) {
                    expr ih_param = mk_local_from_binding(ih_type);
                    ih_params.push_back(ih_param);
                    ih_type = instantiate(binding_body(ih_type), ih_param);
                }
                buffer<expr> new_C_args;
                get_app_args(ih_type, new_C_args);
                expr new_C_pre   = mk_app(new_motive, new_C_args);
                expr new_C       = mk_app(new_C_pre, mk_app(recursive_param, ih_params));
                expr new_ih_type = Pi(ih_params, new_C);
                expr new_ih      = update_mlocal(local, new_ih_type);
                new_minor_params.push_back(new_ih);
                expr h_type = mlocal_type(recursive_param);
                while (is_pi(h_type))
                    h_type = binding_body(h_type);
                h_type = instantiate_rev(h_type, ih_params);
                expr h           = mk_local(mk_fresh_name(), "_h", h_type, binder_info());
                expr app_ih_type = Pi(ih_params, Pi(h, mk_app(new_C_pre, h)));
                expr app_ih      = update_mlocal(local, app_ih_type);
                app_params.push_back(app_ih);
                app_args.push_back(Fun(ih_params, mk_app(mk_app(app_ih, ih_params), mk_app(recursive_param, ih_params))));
            }
            j++;
            minor_type      = instantiate(binding_body(minor_type), local);
        }
        lean_assert(new_minor_params.size() == num_fields + recursive_params.size());
        buffer<expr> new_C_args;
        get_app_args(minor_type, new_C_args);
        expr constructor_app = mk_app(mk_app(mk_constant(ir_name, I_lvls), num_params, rec_params.data()),
                                      num_fields, new_minor_params.data());
        new_C_args.push_back(constructor_app);
        expr new_C = mk_app(new_motive, new_C_args);
        expr new_minor_type  = Pi(new_minor_params, new_C);
        expr new_minor       = update_mlocal(minor, new_minor_type);
        drec_params.push_back(new_minor);
        expr _h_type         = tc.infer(constructor_app);
        expr _h              = mk_local(mk_fresh_name(), "_", _h_type, binder_info());
        rec_args.push_back(Fun(app_params, Fun(_h, mk_app(new_minor, app_args))));
        i++;
    }

    // Add indices and major-premise to rec_args
    for (unsigned i = 0; i < num_idx_major; i++) {
        drec_params.push_back(rec_params[num_params + 1 + num_minors + i]);
        rec_args.push_back(rec_params[num_params + 1 + num_minors + i]);
    }
    // Add major again
    rec_args.push_back(rec_params[major_idx]);

    buffer<expr> new_C_args;
    get_app_args(rec_type, new_C_args);
    expr drec_type  = Pi(drec_params, mk_app(mk_app(new_motive, new_C_args), rec_params[major_idx]));
    expr drec_value = Fun(drec_params, mk_app(rec_cnst, rec_args));
    name drec_name  = name(n, "drec");
    declaration new_d = mk_definition_inferring_trusted(env, drec_name, rec_decl.get_univ_params(),
                                                        drec_type, drec_value,
                                                        reducibility_hints::mk_abbreviation());
    environment new_env = module::add(env, check(env, new_d));
    new_env = set_reducible(new_env, drec_name, reducible_status::Reducible, true);
    new_env = add_aux_recursor(new_env, drec_name);
    return add_protected(new_env, drec_name);
}
}

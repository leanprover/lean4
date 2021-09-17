/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "kernel/kernel_exception.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive.h"
#include "library/suffixes.h"
#include "library/protected.h"
#include "library/reducible.h"
#include "library/constants.h"
#include "library/aux_recursors.h"
#include "library/constructions/util.h"

namespace lean {
/** \brief Given a `C := As -> Type`, return `As -> unit` */
static expr mk_pi_unit(expr const & C, expr const & unit) {
    if (is_pi(C)) {
        return mk_pi(binding_name(C), binding_domain(C), mk_pi_unit(binding_body(C), unit));
    } else {
        return unit;
    }
}

/** \brief Given a `C := As -> Type`, return `fun (xs : As), unit` */
static expr mk_fun_unit(expr const & C, expr const & unit) {
    if (is_pi(C)) {
        return mk_lambda(binding_name(C), binding_domain(C), mk_fun_unit(binding_body(C), unit));
    } else {
        return unit;
    }
}

static bool is_type_former_arg(buffer<name> const & C_ids, expr const & arg) {
    expr const & fn = get_app_fn(arg);
    return is_fvar(fn) && std::find(C_ids.begin(), C_ids.end(), fvar_name(fn)) != C_ids.end();
}

environment mk_cases_on(environment const & env, name const & n) {
    constant_info ind_info = env.get(n);
    if (!ind_info.is_inductive())
        throw exception(sstream() << "error in '" << g_cases_on << "' generation, '" << n << "' is not an inductive datatype");
    name cases_on_name(n, g_cases_on);
    local_ctx lctx;
    inductive_val ind_val  = ind_info.to_inductive_val();
    name_generator ngen    = mk_constructions_name_generator();
    name rec_name          = mk_rec_name(n);
    constant_info rec_info = env.get(rec_name);
    lean_assert(rec_info.is_recursor());
    recursor_val rec_val   = rec_info.to_recursor_val();
    unsigned num_indices   = rec_val.get_nindices();
    unsigned num_minors    = rec_val.get_nminors();
    unsigned num_motives   = rec_val.get_nmotives();
    unsigned num_params    = rec_val.get_nparams();
    buffer<name> ind_names;
    to_buffer(rec_val.get_all(), ind_names);
    /* Populate `rec_fvars` with a free variable for each recursor argument */
    buffer<expr> rec_fvars;
    expr rec_type = rec_info.get_type();
    while (is_pi(rec_type)) {
        expr local = lctx.mk_local_decl(ngen, binding_name(rec_type), binding_domain(rec_type), binding_info(rec_type));
        rec_type   = instantiate(binding_body(rec_type), local);
        rec_fvars.push_back(local);
    }
    /* Remark `rec_fvars` free variables represent the recursor:
       - Type parameters `As` (size == `num_params`)
       - Motives `Cs`         (size == `num_motives`)
       - Minor premises       (size == `num_minors`)
       - Indices              (size == `num_indices`)
       - Major premise        (size == 1)

       The new `cases_on` recursor will have
       - Type parameters `As` (size == `num_params`)
       - Motive C[i]          (size == 1)
       - Minor premises C[i]  (size == number of constructors of the main type)
       - Indices              (size == `num_indices`)
       - Major premise        (size == 1)
    */

    /* Universe levels */
    levels lvls       = lparams_to_levels(rec_info.get_lparams());
    bool elim_to_prop = rec_info.get_num_lparams() == ind_info.get_num_lparams();
    level elim_lvl    = elim_to_prop ? mk_level_zero() : head(lvls);
    /* We need `unit` when `num_motives` > 0 */
    expr unit         = mk_unit(elim_lvl);
    expr star         = mk_unit_mk(elim_lvl);

    buffer<expr> cases_on_params;
    expr rec_cnst = mk_constant(rec_name, lvls);
    buffer<expr> rec_args; // arguments for rec used to define cases_on

    /* Add type parameters `As` */
    for (unsigned i = 0; i < num_params; i++) {
        cases_on_params.push_back(rec_fvars[i]);
        rec_args.push_back(rec_fvars[i]);
    }

    /* Add C[i] */
    buffer<name> C_ids; // unique ids of all motives (aka type formers)
    unsigned i = num_params;
    name C_main_id; // unique id of the main type former
    for (unsigned j = 0; j < num_motives; j++) {
        C_ids.push_back(fvar_name(rec_fvars[i]));
        if (j < ind_names.size() && ind_names[j] == n) {
            cases_on_params.push_back(rec_fvars[i]);
            rec_args.push_back(rec_fvars[i]);
            C_main_id = fvar_name(rec_fvars[i]);
        } else {
            rec_args.push_back(mk_fun_unit(lctx.get_type(rec_fvars[i]), unit));
        }
        i++;
    }

    /* Add indices and major-premise */
    for (unsigned i = 0; i < num_indices + 1; i++)
        cases_on_params.push_back(rec_fvars[num_params + num_motives + num_minors + i]);

    /* Add minor premises */
    auto process_minor = [&](expr const & minor, bool is_main) {
        buffer<expr> minor_non_rec_params;
        buffer<expr> minor_params;
        local_decl minor_decl = lctx.get_local_decl(minor);
        expr minor_type       = minor_decl.get_type();
        while (is_pi(minor_type)) {
            expr curr_type = binding_domain(minor_type);
            expr local     = lctx.mk_local_decl(ngen, binding_name(minor_type), curr_type, binding_info(minor_type));
            expr it        = curr_type;
            while (is_pi(it))
                it = binding_body(it);
            if (is_type_former_arg(C_ids, it)) {
                if (fvar_name(get_app_fn(it)) == C_main_id) {
                    minor_params.push_back(local);
                } else {
                    expr new_local = lctx.mk_local_decl(ngen, binding_name(minor_type), mk_pi_unit(curr_type, unit),
                                                        binding_info(minor_type));
                    minor_params.push_back(new_local);
                }
            } else {
                minor_params.push_back(local);
                if (is_main) minor_non_rec_params.push_back(local);
            }
            minor_type = instantiate(binding_body(minor_type), local);
        }
        if (is_main) {
            expr new_C = lctx.mk_local_decl(ngen, minor_decl.get_user_name(), lctx.mk_pi(minor_non_rec_params, minor_type),
                                            minor_decl.get_info());
            cases_on_params.push_back(new_C);
            expr new_C_app = mk_app(new_C, minor_non_rec_params);
            expr rec_arg   = lctx.mk_lambda(minor_params, new_C_app);
            rec_args.push_back(rec_arg);
        } else {
            rec_args.push_back(lctx.mk_lambda(minor_params, star));
        }
    };
    unsigned minor_idx = 0;
    for (name const & J_name : ind_names) {
        constant_info J_info = env.get(J_name);
        lean_assert(J_info.is_inductive());
        inductive_val J_val  = J_info.to_inductive_val();
        unsigned num_cnstrs = length(J_val.get_cnstrs());
        for (unsigned i = 0; i < num_cnstrs; i++) {
            expr minor = rec_fvars[num_params + num_motives + minor_idx];
            process_minor(minor, J_name == n);
            minor_idx++;
        }
    }
    for (; minor_idx < num_minors; minor_idx++) {
        expr minor = rec_fvars[num_params + num_motives + minor_idx];
        process_minor(minor, false);
    }

    /* Add indices and major-premise to rec_args */
    for (unsigned i = 0; i < num_indices+1; i++)
        rec_args.push_back(rec_fvars[num_params + num_motives + num_minors + i]);

    expr cases_on_type  = lctx.mk_pi(cases_on_params, rec_type);
    expr cases_on_value = lctx.mk_lambda(cases_on_params,  mk_app(rec_cnst, rec_args));
    declaration new_d = mk_definition_inferring_unsafe(env, cases_on_name, rec_info.get_lparams(), cases_on_type, cases_on_value,
                                                       reducibility_hints::mk_abbreviation());
    environment new_env = env.add(new_d);
    new_env = set_reducible(new_env, cases_on_name, reducible_status::Reducible, true);
    new_env = add_aux_recursor(new_env, cases_on_name);
    return add_protected(new_env, cases_on_name);
}

extern "C" LEAN_EXPORT object * lean_mk_cases_on(object * env, object * n) {
    return catch_kernel_exceptions<environment>([&]() { return mk_cases_on(environment(env), name(n, true)); });
}
}

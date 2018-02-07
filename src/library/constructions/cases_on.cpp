/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/reducible.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/aux_recursors.h"
#include "library/scoped_ext.h"
#include "library/constructions/util.h"

namespace lean {
static bool is_type_former_arg(name const & C_name, expr const & arg) {
    expr const & fn = get_app_fn(arg);
    return is_local(fn) && mlocal_name(fn) == C_name;
}

environment mk_cases_on(environment const & env, name const & n) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl)
        throw exception(sstream() << "error in 'cases_on' generation, '" << n << "' is not an inductive datatype");
    // TODO(Leo): cleanup, this code still has leftovers from the time the kernel had support for
    // mutually inductive types
    name cases_on_name(n, "cases_on");
    name_generator ngen    = mk_constructions_name_generator();
    name rec_name          = inductive::get_elim_name(n);
    declaration rec_decl   = env.get(rec_name);
    declaration ind_decl   = env.get(n);
    unsigned num_idx_major = *inductive::get_num_indices(env, n) + 1;
    unsigned num_minors    = *inductive::get_num_minor_premises(env, n);
    unsigned num_params    = decl->m_num_params;
    buffer<expr> rec_params;
    expr rec_type = rec_decl.get_type();
    while (is_pi(rec_type)) {
        expr local = mk_local(ngen.next(), binding_name(rec_type), binding_domain(rec_type), binding_info(rec_type));
        rec_type   = instantiate(binding_body(rec_type), local);
        rec_params.push_back(local);
    }

    levels lvls       = param_names_to_levels(rec_decl.get_univ_params());
    bool elim_to_prop = rec_decl.get_num_univ_params() == ind_decl.get_num_univ_params();
    level elim_univ   = elim_to_prop ? mk_level_zero() : head(lvls);

    optional<expr> unit;
    optional<expr> star;

    buffer<expr> cases_on_params;
    expr rec_cnst = mk_constant(rec_name, lvls);
    buffer<expr> rec_args; // arguments for rec used to define cases_on

    // Add params: As
    for (unsigned i = 0; i < num_params; i++) {
        cases_on_params.push_back(rec_params[i]);
        rec_args.push_back(rec_params[i]);
    }

    // Add movite C
    unsigned i = num_params;
    cases_on_params.push_back(rec_params[i]);
    rec_args.push_back(rec_params[i]);
    name C_main = mlocal_name(rec_params[i]);
    i++;

    // Add indices and major-premise to rec_params
    for (unsigned i = 0; i < num_idx_major; i++)
        cases_on_params.push_back(rec_params[num_params + 1 + num_minors + i]);
    // Add minor premises to rec_params and rec_args
    i = num_params + 1;
    for (auto ir : decl->m_intro_rules) {
        expr const & minor = rec_params[i];
        // A cases_on minor premise does not contain "recursive" arguments
        buffer<expr> minor_non_rec_params;
        buffer<expr> minor_params;
        expr minor_type = mlocal_type(minor);
        while (is_pi(minor_type)) {
            expr local = mk_local(ngen.next(), binding_name(minor_type), binding_domain(minor_type),
                                  binding_info(minor_type));
            expr curr_type = mlocal_type(local);
            while (is_pi(curr_type))
                curr_type = binding_body(curr_type);
            if (is_type_former_arg(C_main, curr_type)) {
                minor_params.push_back(local);
            } else {
                minor_params.push_back(local);
                minor_non_rec_params.push_back(local);
            }
            minor_type = instantiate(binding_body(minor_type), local);
        }
        expr new_C = update_mlocal(minor, Pi(minor_non_rec_params, minor_type));
        cases_on_params.push_back(new_C);
        expr new_C_app = mk_app(new_C, minor_non_rec_params);
        expr rec_arg   = Fun(minor_params, new_C_app);
        rec_args.push_back(rec_arg);
        i++;
    }

    // Add indices and major-premise to rec_args
    for (unsigned i = 0; i < num_idx_major; i++)
        rec_args.push_back(rec_params[num_params + 1 + num_minors + i]);

    expr cases_on_type  = Pi(cases_on_params, rec_type);
    expr cases_on_value = Fun(cases_on_params,  mk_app(rec_cnst, rec_args));

    declaration new_d = mk_definition_inferring_trusted(env, cases_on_name, rec_decl.get_univ_params(), cases_on_type, cases_on_value,
                                                        reducibility_hints::mk_abbreviation());
    environment new_env = module::add(env, check(env, new_d));
    new_env = set_reducible(new_env, cases_on_name, reducible_status::Reducible, true);
    new_env = add_aux_recursor(new_env, cases_on_name);
    return add_protected(new_env, cases_on_name);
}
}

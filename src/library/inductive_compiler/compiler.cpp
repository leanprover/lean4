/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "util/sexpr/option_declarations.h"
#include "library/locals.h"
#include "library/module.h"
#include "library/attribute_manager.h"
#include "library/inductive_compiler/compiler.h"
#include "library/constructions/rec_on.h"
#include "library/constructions/induction_on.h"
#include "library/constructions/cases_on.h"
#include "library/constructions/brec_on.h"
#include "library/constructions/no_confusion.h"

#ifndef LEAN_DEFAULT_XINDUCTIVE_REC_ON
#define LEAN_DEFAULT_XINDUCTIVE_REC_ON true
#endif

#ifndef LEAN_DEFAULT_XINDUCTIVE_CASES_ON
#define LEAN_DEFAULT_XINDUCTIVE_CASES_ON true
#endif

#ifndef LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION
#define LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION true
#endif

#ifndef LEAN_DEFAULT_XINDUCTIVE_BREC_ON
#define LEAN_DEFAULT_XINDUCTIVE_BREC_ON true
#endif

namespace lean {

static name * g_inductive_rec_on       = nullptr;
static name * g_inductive_cases_on     = nullptr;
static name * g_inductive_no_confusion = nullptr;
static name * g_inductive_brec_on      = nullptr;

static bool get_inductive_rec_on(options const & opts) {
    return opts.get_bool(*g_inductive_rec_on, LEAN_DEFAULT_XINDUCTIVE_REC_ON);
}

static bool get_inductive_cases_on(options const & opts) {
    return opts.get_bool(*g_inductive_cases_on, LEAN_DEFAULT_XINDUCTIVE_CASES_ON);
}

static bool get_inductive_brec_on(options const & opts) {
    return opts.get_bool(*g_inductive_brec_on, LEAN_DEFAULT_XINDUCTIVE_BREC_ON);
}

static bool get_inductive_no_confusion(options const & opts) {
    return opts.get_bool(*g_inductive_no_confusion, LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION);
}

using inductive::inductive_decl;
using inductive::intro_rule;
using inductive::mk_intro_rule;

environment tmp_add_kernel_inductive(environment const & env, name_map<implicit_infer_kind> implicit_infer_map,
                                     buffer<name> const & lp_names,
                                     buffer<expr> const & params, expr const & ind, buffer<expr> const & intro_rules) {
    expr new_ind_type = Pi(params, mlocal_type(ind));
    expr c_ind = mk_app(mk_constant(mlocal_name(ind), param_names_to_levels(to_list(lp_names))), params);

    buffer<intro_rule> new_intro_rules;
    for (expr const & ir : intro_rules) {
        expr new_ir_type = Pi(params, replace_local(mlocal_type(ir), ind, c_ind));
        implicit_infer_kind k = *implicit_infer_map.find(mlocal_name(ir));
        new_intro_rules.push_back(mk_intro_rule(mlocal_name(ir), infer_implicit_params(new_ir_type, params.size(), k)));
    }
    inductive_decl decl(mlocal_name(ind), new_ind_type, to_list(new_intro_rules));
    return module::add_inductive(env, to_list(lp_names), params.size(), list<inductive_decl>(decl));
}

environment mk_basic_aux_decls(environment env, options const & opts, name const & ind_name) {
    bool has_unit = has_poly_unit_decls(env);
    bool has_eq   = has_eq_decls(env);
    bool has_heq  = has_heq_decls(env);
    bool has_prod = has_prod_decls(env);
    bool has_lift = has_lift_decls(env);

    bool gen_rec_on       = get_inductive_rec_on(opts);
    bool gen_brec_on      = get_inductive_brec_on(opts);
    bool gen_cases_on     = get_inductive_cases_on(opts);
    bool gen_no_confusion = get_inductive_no_confusion(opts);

    if (gen_rec_on)
        env = mk_rec_on(env, ind_name);

    if (gen_rec_on && env.impredicative())
        env = mk_induction_on(env, ind_name);

    if (has_unit) {
        if (gen_cases_on)
            env = mk_cases_on(env, ind_name);

        if (gen_cases_on && gen_no_confusion && has_eq
            && ((env.prop_proof_irrel() && has_heq) || (!env.prop_proof_irrel() && has_lift))) {
                env = mk_no_confusion(env, ind_name);
        }

        if (gen_brec_on && has_prod) {
            env = mk_below(env, ind_name);
            if (env.impredicative()) {
                env = mk_ibelow(env, ind_name);
            }
        }
    }

    if (gen_brec_on && has_unit && has_prod) {
        env = mk_brec_on(env, ind_name);
        if (env.impredicative()) {
            env = mk_binduction_on(env, ind_name);
        }
    }
    return env;
}

environment add_inductive_declaration(environment const & old_env, options const & opts,
                                      name_map<implicit_infer_kind> implicit_infer_map,
                                      buffer<name> const & lp_names, buffer<expr> const & params,
                                      buffer<expr> const & inds, buffer<buffer<expr> > const & intro_rules) {
    // TODO(dhs): mutual and nested inductive types
    lean_assert(inds.size() == 1);
    lean_assert(intro_rules.size() == 1);

    environment env = tmp_add_kernel_inductive(old_env, implicit_infer_map, lp_names, params, inds[0], intro_rules[0]);
    env = mk_basic_aux_decls(env, opts, mlocal_name(inds[0]));
    return env;
}


void initialize_inductive_compiler() {
    g_inductive_rec_on       = new name{"inductive", "rec_on"};
    g_inductive_cases_on     = new name{"inductive", "cases_on"};
    g_inductive_brec_on      = new name{"inductive", "brec_on"};
    g_inductive_no_confusion = new name{"inductive", "no_confusion"};

    register_bool_option(*g_inductive_rec_on, LEAN_DEFAULT_XINDUCTIVE_REC_ON,
                         "(inductive) automatically generate the auxiliary declarations C.rec_on and C.induction_on  for each inductive datatype C");

    register_bool_option(*g_inductive_brec_on, LEAN_DEFAULT_XINDUCTIVE_BREC_ON,
                         "(inductive) automatically generate the auxiliary declaration C.brec_on for each inductive datatype C");

    register_bool_option(*g_inductive_cases_on, LEAN_DEFAULT_XINDUCTIVE_CASES_ON,
                         "(inductive) automatically generate the auxiliary declaration C.cases_on for each inductive datatype C"
                         "(remark: if cases_on is disabled, then the auxiliary declaration C.no_confusion is also disabled");

    register_bool_option(*g_inductive_no_confusion, LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION,
                         "(inductive) automatically generate the auxiliary declaration C.no_confusion for each inductive datatype C");
}

void finalize_inductive_compiler() {
    delete g_inductive_rec_on;
    delete g_inductive_cases_on;
    delete g_inductive_brec_on;
    delete g_inductive_no_confusion;
}

}

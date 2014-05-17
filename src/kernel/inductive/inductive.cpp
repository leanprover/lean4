/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_generator.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"

namespace lean {
namespace inductive {
static name g_tmp_prefix = name::mk_internal_unique_name();

environment add_inductive(environment const & env, name const & ind_name, level_param_names const & level_params,
                          unsigned num_params, expr const & type, list<intro_rule> const & intro_rules) {
    return add_inductive(env, level_params, num_params, list<inductive_decl>(inductive_decl(ind_name, type, intro_rules)));
}

environment add_inductive(environment                  env,
                          level_param_names const &    level_params,
                          unsigned                     num_params,
                          list<inductive_decl> const & decls) {
    // TODO(Leo)
    std::cout << "\nadd_inductive\n";
    if (!is_nil(level_params)) {
        std::cout << "level params: ";
        for (auto l : level_params) { std::cout << l << " "; }
        std::cout << "\n";
    }
    std::cout << "num params: " << num_params << "\n";
    for (auto d : decls) {
        std::cout << inductive_decl_name(d) << " : " << inductive_decl_type(d) << "\n";
        for (auto ir : inductive_decl_intros(d)) {
            std::cout << "  " << intro_rule_name(ir) << " : " << intro_rule_type(ir) << "\n";
        }
    }
    if (is_nil(decls))
        throw kernel_exception(env, "at least one inductive datatype declaration expected");

    type_checker  tc(env);
    bool first = true;
    buffer<expr>  param_types;
    buffer<expr>  local_consts;
    buffer<level> Ilevels; // level of each inductive datatype
    name_generator ngen(g_tmp_prefix);

    // Check if the type of datatypes is well typed
    for (auto d : decls) {
        expr t = tc.whnf(inductive_decl_type(d));
        tc.check(t, level_params);
        unsigned i  = 0;
        while (is_pi(t)) {
            if (i < num_params) {
                if (first) {
                    param_types.push_back(binding_domain(t));
                    expr l = mk_local(ngen.next(), binding_name(t), binding_domain(t));
                    local_consts.push_back(l);
                    t = instantiate(binding_body(t), l);
                } else {
                    if (!tc.is_def_eq(binding_domain(t), param_types[i]))
                        throw kernel_exception(env, "parameters of all inductive datatypes must match");
                    t = instantiate(binding_body(t), local_consts[i]);
                }
                i++;
            } else {
                t = binding_body(t);
            }
            t = tc.whnf(t);
        }
        first = false;
        if (i != num_params)
            throw kernel_exception(env, "number of parameters mismatch in inductive datatype declaration");
        t = tc.ensure_sort(t);
        Ilevels.push_back(sort_level(t));
    }

    // Add all datatype declarations to environment
    for (auto d : decls) {
        env = env.add(check(env, mk_var_decl(inductive_decl_name(d), level_params, inductive_decl_type(d))));
    }
    // Add all introduction rules (aka constructors) to environment
    for (auto d : decls) {
        for (auto ir : inductive_decl_intros(d))
            env = env.add(check(env, mk_var_decl(intro_rule_name(ir), level_params, intro_rule_type(ir))));
    }
    return env;
}
}
}

/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"

namespace lean {
namespace inductive {
environment add_inductive(environment const & env,  name const & ind_name, level_param_names const & level_params,
                          telescope const & params, telescope const & indices, list<intro_rule> const & intro_rules,
                          optional<unsigned> const & univ_offset) {
    return add_inductive(env, level_params, params, list<inductive_decl>(std::make_tuple(ind_name, indices, intro_rules)), univ_offset);
}

environment add_inductive(environment const &          env,
                          level_param_names const &    level_params,
                          telescope const &            params,
                          list<inductive_decl> const & decls,
                          optional<unsigned> const &   univ_offset) {
    // TODO(Leo)
    std::cout << "add_inductive\n";
    if (!is_nil(level_params)) { for (auto l : level_params) { std::cout << l << " "; } std::cout << "\n"; }
    if (!is_nil(params)) { for (auto e : params) { std::cout << e.get_name() << " "; } std::cout << "\n"; }
    for (auto d : decls) {
        std::cout << inductive_decl_name(d) << "\n";
        for (auto ir : inductive_decl_intros(d)) {
            std::cout << "  " << intro_rule_name(ir) << " #" << length(intro_rule_args(ir)) << " " << intro_rule_type(ir) << "\n";
        }
    }
    if (univ_offset) std::cout << "offset: " << *univ_offset << "\n";
    return env;
}
}
}

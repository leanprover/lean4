/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"

namespace lean {
namespace inductive {
environment add_inductive(environment const & env,  name const & ind_name, level_params const & level_params,
                          telescope const & params, telescope const & indices, list<intro_rule> const & intro_rules,
                          optional<unsigned> const & univ_offset) {
    return add_inductive(env, level_params, params, list<inductive_decl>(std::make_tuple(ind_name, indices, intro_rules)), univ_offset);
}

environment add_inductive(environment const &          env,
                          level_params const &         level_params,
                          telescope const &            params,
                          list<inductive_decl> const & decls,
                          optional<unsigned> const &   univ_offset) {
    // TODO(Leo)
    std::cout << "add_inductive\n";
    for (auto l : level_params) { std::cout << l << " "; } std::cout << "\n";
    for (auto e : params) { std::cout << std::get<0>(e) << " "; } std::cout << "\n";
    for (auto d : decls) { std::cout << std::get<0>(d) << " "; } std::cout << "\n";
    if (univ_offset) std::cout << "offset: " << *univ_offset << "\n";
    return env;
}
}
}

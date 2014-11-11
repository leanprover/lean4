/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/find_fn.h"
#include "kernel/inductive/inductive.h"

namespace lean {
bool is_recursive_datatype(environment const & env, name const & n) {
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        return false;
    for (inductive::inductive_decl const & decl : std::get<2>(*decls)) {
        for (inductive::intro_rule const & intro : inductive::inductive_decl_intros(decl)) {
            expr type = inductive::intro_rule_type(intro);
            while (is_pi(type)) {
                if (find(binding_domain(type), [&](expr const & e, unsigned) {
                            return is_constant(e) && const_name(e) == n; }))
                    return true;
                type = binding_body(type);
            }
        }
    }
    return false;
}

bool is_inductive_predicate(environment const & env, name const & n) {
    if (!env.impredicative())
        return false; // environment does not have Prop
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    expr type = env.get(n).get_type();
    while (is_pi(type)) {
        type = binding_body(type);
    }
    return is_sort(type) && is_zero(sort_level(type));
}
}

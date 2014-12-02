/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"

namespace lean {
/** \brief Return true if environment has a constructor named \c c that returns
    an element of the inductive datatype named \c I, and \c c must have \c nparams parameters.
*/
bool has_constructor(environment const & env, name const & c, name const & I, unsigned nparams) {
    auto d = env.find(c);
    if (!d || d->is_definition())
        return false;
    expr type = d->get_type();
    unsigned i = 0;
    while (is_pi(type)) {
        i++;
        type = binding_body(type);
    }
    if (i != nparams)
        return false;
    type = get_app_fn(type);
    return is_constant(type) && const_name(type) == I;
}

bool has_unit_decls(environment const & env) {
    return has_constructor(env, name{"unit", "star"}, "unit", 0);
}

bool has_eq_decls(environment const & env) {
    return has_constructor(env, name{"eq", "refl"}, "eq", 2);
}

bool has_heq_decls(environment const & env) {
    return has_constructor(env, name{"heq", "refl"}, "heq", 2);
}

bool has_prod_decls(environment const & env) {
    return has_constructor(env, name{"prod", "mk"}, "prod", 4);
}

bool is_recursive_datatype(environment const & env, name const & n) {
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        return false;
    for (inductive::inductive_decl const & decl : std::get<2>(*decls)) {
        for (inductive::intro_rule const & intro : inductive::inductive_decl_intros(decl)) {
            expr type = inductive::intro_rule_type(intro);
            while (is_pi(type)) {
                if (find(binding_domain(type), [&](expr const & e, unsigned) {
                            return is_constant(e) && const_name(e) == n; })) {
                    return true;
                }
                type = binding_body(type);
            }
        }
    }
    return false;
}

bool is_reflexive_datatype(type_checker & tc, name const & n) {
    environment const & env = tc.env();
    name_generator ngen     = tc.mk_ngen();
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        return false;
    for (inductive::inductive_decl const & decl : std::get<2>(*decls)) {
        for (inductive::intro_rule const & intro : inductive::inductive_decl_intros(decl)) {
            expr type = inductive::intro_rule_type(intro);
            while (is_pi(type)) {
                expr arg   = tc.whnf(binding_domain(type)).first;
                if (is_pi(arg) && find(arg, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; })) {
                    return true;
                }
                expr local = mk_local(ngen.next(), binding_domain(type));
                type = instantiate(binding_body(type), local);
            }
        }
    }
    return false;
}

level get_datatype_level(expr ind_type) {
    while (is_pi(ind_type))
        ind_type = binding_body(ind_type);
    return sort_level(ind_type);
}

bool is_inductive_predicate(environment const & env, name const & n) {
    if (!env.impredicative())
        return false; // environment does not have Prop
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    return is_zero(get_datatype_level(env.get(n).get_type()));
}

expr instantiate_univ_param (expr const & e, name const & p, level const & l) {
    return instantiate_univ_params(e, to_list(p), to_list(l));
}

expr to_telescope(name_generator & ngen, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    while (is_pi(type)) {
        expr local;
        if (binfo)
            local = mk_local(ngen.next(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(ngen.next(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type = instantiate(binding_body(type), local);
    }
    return type;
}

expr to_telescope(type_checker & tc, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    type = tc.whnf(type).first;
    while (is_pi(type)) {
        expr local;
        if (binfo)
            local = mk_local(tc.mk_fresh_name(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(tc.mk_fresh_name(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type = tc.whnf(instantiate(binding_body(type), local)).first;
    }
    return type;
}
}

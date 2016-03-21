/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/metavar.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/unfold_macros.h"
#include "library/pp_options.h"
#include "library/projection.h"
#include "library/old_type_checker.h"

namespace lean {
bool is_app_of(expr const & t, name const & f_name) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name;
}

bool is_app_of(expr const & t, name const & f_name, unsigned nargs) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name && get_app_num_args(t) == nargs;
}

bool is_standard(environment const & env) {
    return env.prop_proof_irrel() && env.impredicative();
}

optional<expr> unfold_term(environment const & env, expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return none_expr();
    expr d = instantiate_value_univ_params(*decl, const_levels(f));
    buffer<expr> args;
    get_app_rev_args(e, args);
    return some_expr(apply_beta(d, args.size(), args.data()));
}

optional<expr> unfold_app(environment const & env, expr const & e) {
    if (!is_app(e))
        return none_expr();
    return unfold_term(env, e);
}

optional<level> dec_level(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Global: case level_kind::Meta:
        return none_level();
    case level_kind::Succ:
        return some_level(succ_of(l));
    case level_kind::Max:
        if (auto lhs = dec_level(max_lhs(l))) {
        if (auto rhs = dec_level(max_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    case level_kind::IMax:
        // Remark: the following mk_max is not a typo. The following
        // assertion justifies it.
        if (auto lhs = dec_level(imax_lhs(l))) {
        if (auto rhs = dec_level(imax_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

/** \brief Return true if environment has a constructor named \c c that returns
    an element of the inductive datatype named \c I, and \c c must have \c nparams parameters. */
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

bool has_poly_unit_decls(environment const & env) {
    return has_constructor(env, get_poly_unit_star_name(), get_poly_unit_name(), 0);
}

bool has_eq_decls(environment const & env) {
    return has_constructor(env, get_eq_refl_name(), get_eq_name(), 2);
}

bool has_heq_decls(environment const & env) {
    return has_constructor(env, get_heq_refl_name(), get_heq_name(), 2);
}

bool has_prod_decls(environment const & env) {
    return has_constructor(env, get_prod_mk_name(), get_prod_name(), 4);
}

bool has_lift_decls(environment const & env) {
    return has_constructor(env, get_lift_up_name(), get_lift_name(), 2);
}

/* n is considered to be recursive if it is an inductive datatype and
   1) It has a constructor that takes n as an argument
   2) It is part of a mutually recursive declaration, and some constructor
      of an inductive datatype takes another inductive datatype from the
      same declaration as an argument. */
bool is_recursive_datatype(environment const & env, name const & n) {
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        return false;
    for (inductive::inductive_decl const & decl : std::get<2>(*decls)) {
        for (inductive::intro_rule const & intro : inductive::inductive_decl_intros(decl)) {
            expr type = inductive::intro_rule_type(intro);
            while (is_pi(type)) {
                if (find(binding_domain(type), [&](expr const & e, unsigned) {
                            if (is_constant(e)) {
                                name const & c = const_name(e);
                                for (auto const & d : std::get<2>(*decls)) {
                                    if (inductive::inductive_decl_name(d) == c)
                                        return true;
                                }
                            }
                            return false;
                        })) {
                    return true;
                }
                type = binding_body(type);
            }
        }
    }
    return false;
}

bool is_reflexive_datatype(abstract_type_context & tc, name const & n) {
    environment const & env = tc.env();
    optional<inductive::inductive_decls> decls = inductive::is_inductive_decl(env, n);
    if (!decls)
        return false;
    for (inductive::inductive_decl const & decl : std::get<2>(*decls)) {
        for (inductive::intro_rule const & intro : inductive::inductive_decl_intros(decl)) {
            expr type = inductive::intro_rule_type(intro);
            while (is_pi(type)) {
                expr arg   = tc.whnf(binding_domain(type));
                if (is_pi(arg) && find(arg, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; })) {
                    return true;
                }
                expr local = mk_local(mk_fresh_name(), binding_domain(type));
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
    if (!is_standard(env))
        return false;
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    return is_zero(get_datatype_level(env.get(n).get_type()));
}

void get_intro_rule_names(environment const & env, name const & n, buffer<name> & result) {
    if (auto decls = inductive::is_inductive_decl(env, n)) {
        for (inductive::inductive_decl const & decl : std::get<2>(*decls)) {
            if (inductive::inductive_decl_name(decl) == n) {
                for (inductive::intro_rule const & ir : inductive::inductive_decl_intros(decl))
                    result.push_back(inductive::intro_rule_name(ir));
                return;
            }
        }
    }
}

optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn))
        if (auto I = inductive::is_intro_rule(env, const_name(fn)))
            return optional<name>(const_name(fn));
    return optional<name>();
}

optional<name> is_constructor_app_ext(environment const & env, expr const & e) {
    if (auto r = is_constructor_app(env, e))
        return r;
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return optional<name>();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return optional<name>();
    expr const * it = &decl->get_value();
    while (is_lambda(*it))
        it = &binding_body(*it);
    return is_constructor_app_ext(env, *it);
}

expr instantiate_univ_param (expr const & e, name const & p, level const & l) {
    return instantiate_univ_params(e, to_list(p), to_list(l));
}

expr to_telescope(bool pi, expr e, buffer<expr> & telescope,
                  optional<binder_info> const & binfo) {
    while ((pi && is_pi(e)) || (!pi && is_lambda(e))) {
        expr local;
        if (binfo)
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), *binfo);
        else
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
        telescope.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    return e;
}

expr to_telescope(expr const & type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    return to_telescope(true, type, telescope, binfo);
}

expr fun_to_telescope(expr const & e, buffer<expr> & telescope,
                      optional<binder_info> const & binfo) {
    return to_telescope(false, e, telescope, binfo);
}

format pp_type_mismatch(formatter const & fmt, expr const & v, expr const & v_type, expr const & t) {
    format expected_fmt, given_fmt;
    std::tie(expected_fmt, given_fmt) = pp_until_different(fmt, t, v_type);
    format r("type mismatch at term");
    r += pp_indent_expr(fmt, v);
    r += compose(line(), format("has type"));
    r += given_fmt;
    r += compose(line(), format("but is expected to have type"));
    r += expected_fmt;
    return r;
}

void initialize_library_util() {
}

void finalize_library_util() {
}
}

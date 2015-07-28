/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/default_converter.h"
#include "kernel/metavar.h"
#include "kernel/inductive/inductive.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/unfold_macros.h"
#include "library/pp_options.h"
#include "library/projection.h"

namespace lean {
bool is_standard(environment const & env) {
    return env.prop_proof_irrel() && env.impredicative();
}

bool is_norm_pi(type_checker & tc, expr & e, constraint_seq & cs) {
    constraint_seq new_cs = cs;
    expr new_e = tc.whnf(e, new_cs);
    if (is_pi(new_e)) {
        e  = new_e;
        cs = new_cs;
        return true;
    } else {
        return false;
    }
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

// n is considered to be recursive if it is an inductive datatype and
// 1) It has a constructor that takes n as an argument
// 2) It is part of a mutually recursive declaration, and some constructor
//    of an inductive datatype takes another inductive datatype from the
//    same declaration as an argument.
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

expr to_telescope(bool pi, name_generator & ngen, expr e, buffer<expr> & telescope,
                  optional<binder_info> const & binfo) {
    while ((pi && is_pi(e)) || (!pi && is_lambda(e))) {
        expr local;
        if (binfo)
            local = mk_local(ngen.next(), binding_name(e), binding_domain(e), *binfo);
        else
            local = mk_local(ngen.next(), binding_name(e), binding_domain(e), binding_info(e));
        telescope.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    return e;
}

expr to_telescope(name_generator & ngen, expr const & type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    return to_telescope(true, ngen, type, telescope, binfo);
}

expr fun_to_telescope(name_generator & ngen, expr const & e, buffer<expr> & telescope,
                      optional<binder_info> const & binfo) {
    return to_telescope(false, ngen, e, telescope, binfo);
}

expr to_telescope(type_checker & tc, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo,
                  constraint_seq & cs) {
    expr new_type = tc.whnf(type, cs);
    while (is_pi(new_type)) {
        type = new_type;
        expr local;
        if (binfo)
            local = mk_local(tc.mk_fresh_name(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(tc.mk_fresh_name(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type     = instantiate(binding_body(type), local);
        new_type = tc.whnf(type, cs);
    }
    return type;
}

expr to_telescope(type_checker & tc, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    constraint_seq cs;
    return to_telescope(tc, type, telescope, binfo, cs);
}

expr mk_false() {
    return mk_constant(get_false_name());
}

expr mk_empty() {
    return mk_constant(get_empty_name());
}

expr mk_false(environment const & env) {
    return is_standard(env) ? mk_false() : mk_empty();
}

bool is_false(expr const & e) {
    return is_constant(e) && const_name(e) == get_false_name();
}

bool is_empty(expr const & e) {
    return is_constant(e) && const_name(e) == get_empty_name();
}

bool is_false(environment const & env, expr const & e) {
    return is_standard(env) ? is_false(e) : is_empty(e);
}

expr mk_false_rec(type_checker & tc, expr const & f, expr const & t) {
    level t_lvl = sort_level(tc.ensure_type(t).first);
    if (is_standard(tc.env())) {
        return mk_app(mk_constant(get_false_rec_name(), {t_lvl}), t, f);
    } else {
        expr f_type = tc.infer(f).first;
        return mk_app(mk_constant(get_empty_rec_name(), {t_lvl}), mk_lambda("e", f_type, t), f);
    }
}

bool is_not(environment const & env, expr const & e, expr & a) {
    if (is_app(e)) {
        expr const & f = app_fn(e);
        if (!is_constant(f) || const_name(f) != get_not_name())
            return false;
        a = app_arg(e);
        return true;
    } else if (is_pi(e)) {
        if (!is_false(env, binding_body(e)))
            return false;
        a = binding_domain(e);
        return true;
    } else {
        return false;
    }
}

expr mk_not(type_checker & tc, expr const & e) {
    if (is_standard(tc.env())) {
        return mk_app(mk_constant(get_not_name()), e);
    } else {
        level l = sort_level(tc.ensure_type(e).first);
        return mk_app(mk_constant(get_not_name(), {l}), e);
    }
}

expr mk_absurd(type_checker & tc, expr const & t, expr const & e, expr const & not_e) {
    level t_lvl  = sort_level(tc.ensure_type(t).first);
    expr  e_type = tc.infer(e).first;
    if (is_standard(tc.env())) {
        return mk_app(mk_constant(get_absurd_name(), {t_lvl}), e_type, t, e, not_e);
    } else {
        level e_lvl = sort_level(tc.ensure_type(e_type).first);
        return mk_app(mk_constant(get_absurd_name(), {e_lvl, t_lvl}), e_type, t, e, not_e);
    }
}

optional<expr> lift_down_if_hott(type_checker & tc, expr const & v) {
    if (is_standard(tc.env())) {
        return some_expr(v);
    } else {
        expr v_type = tc.whnf(tc.infer(v).first).first;
        if (!is_app(v_type))
            return none_expr();
        expr const & lift = app_fn(v_type);
        if (!is_constant(lift) || const_name(lift) != get_lift_name())
            return none_expr();
        return some_expr(mk_app(mk_constant(get_lift_down_name(), const_levels(lift)), app_arg(v_type), v));
    }
}

static expr * g_true = nullptr;
static expr * g_true_intro = nullptr;
static expr * g_and = nullptr;
static expr * g_and_intro = nullptr;
static expr * g_and_elim_left = nullptr;
static expr * g_and_elim_right = nullptr;

void initialize_library_util() {
    g_true           = new expr(mk_constant(get_true_name()));
    g_true_intro     = new expr(mk_constant(get_true_intro_name()));
    g_and            = new expr(mk_constant(get_and_name()));
    g_and_intro      = new expr(mk_constant(get_and_intro_name()));
    g_and_elim_left  = new expr(mk_constant(get_and_elim_left_name()));
    g_and_elim_right = new expr(mk_constant(get_and_elim_right_name()));
}

void finalize_library_util() {
    delete g_true;
    delete g_true_intro;
    delete g_and;
    delete g_and_intro;
    delete g_and_elim_left;
    delete g_and_elim_right;
}

expr mk_true() {
    return *g_true;
}

expr mk_true_intro() {
    return *g_true_intro;
}

bool is_and(expr const & e, expr & arg1, expr & arg2) {
    if (get_app_fn(e) == *g_and) {
        buffer<expr> args; get_app_args(e, args);
        if (args.size() == 2) {
            arg1 = args[0];
            arg2 = args[1];
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

expr mk_and(expr const & a, expr const & b) {
    return mk_app(*g_and, a, b);
}

expr mk_and_intro(type_checker & tc, expr const & Ha, expr const & Hb) {
    return mk_app(*g_and_intro, tc.infer(Ha).first, tc.infer(Hb).first, Ha, Hb);
}

expr mk_and_elim_left(type_checker & tc, expr const & H) {
    expr a_and_b = tc.whnf(tc.infer(H).first).first;
    return mk_app(*g_and_elim_left, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_and_elim_right(type_checker & tc, expr const & H) {
    expr a_and_b = tc.whnf(tc.infer(H).first).first;
    return mk_app(*g_and_elim_right, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_unit(level const & l) {
    return mk_constant(get_poly_unit_name(), {l});
}

expr mk_unit_mk(level const & l) {
    return mk_constant(get_poly_unit_star_name(), {l});
}

expr mk_prod(type_checker & tc, expr const & A, expr const & B) {
    level l1 = sort_level(tc.ensure_type(A).first);
    level l2 = sort_level(tc.ensure_type(B).first);
    return mk_app(mk_constant(get_prod_name(), {l1, l2}), A, B);
}

expr mk_pair(type_checker & tc, expr const & a, expr const & b) {
    expr A = tc.infer(a).first;
    expr B = tc.infer(b).first;
    level l1 = sort_level(tc.ensure_type(A).first);
    level l2 = sort_level(tc.ensure_type(B).first);
    return mk_app(mk_constant(get_prod_mk_name(), {l1, l2}), A, B, a, b);
}

expr mk_pr1(type_checker & tc, expr const & p) {
    expr AxB = tc.whnf(tc.infer(p).first).first;
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_prod_pr1_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_pr2(type_checker & tc, expr const & p) {
    expr AxB = tc.whnf(tc.infer(p).first).first;
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_prod_pr2_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_unit(level const & l, bool prop) { return prop ? mk_true() : mk_unit(l); }
expr mk_unit_mk(level const & l, bool prop) { return prop ? mk_true_intro() : mk_unit_mk(l); }
expr mk_prod(type_checker & tc, expr const & a, expr const & b, bool prop) { return prop ? mk_and(a, b) : mk_prod(tc, a, b); }
expr mk_pair(type_checker & tc, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and_intro(tc, a, b) : mk_pair(tc, a, b);
}
expr mk_pr1(type_checker & tc, expr const & p, bool prop) { return prop ? mk_and_elim_left(tc, p) : mk_pr1(tc, p); }
expr mk_pr2(type_checker & tc, expr const & p, bool prop) { return prop ? mk_and_elim_right(tc, p) : mk_pr2(tc, p); }

bool is_ite(expr const & e, expr & c, expr & H, expr & A, expr & t, expr & f) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn) && const_name(fn) == get_ite_name()) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() == 5) {
            c = args[0]; H = args[1]; A = args[2]; t = args[3]; f = args[4];
            return true;
        } else {
            return true;
        }
    } else {
        return false;
    }
}

bool is_iff(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_iff_name();
}
expr mk_iff(expr const & lhs, expr const & rhs) {
    return mk_app(mk_constant(get_iff_name()), lhs, rhs);
}
expr mk_iff_refl(expr const & a) {
    return mk_app(mk_constant(get_iff_refl_name()), a);
}
expr apply_propext(expr const & iff_pr, expr const & iff_term) {
    lean_assert(is_iff(iff_term));
    return mk_app(mk_constant(get_propext_name()), app_arg(app_fn(iff_term)), app_arg(iff_term), iff_pr);
}

expr mk_eq(type_checker & tc, expr const & lhs, expr const & rhs) {
    expr A    = tc.whnf(tc.infer(lhs).first).first;
    level lvl = sort_level(tc.ensure_type(A).first);
    return mk_app(mk_constant(get_eq_name(), {lvl}), A, lhs, rhs);
}

expr mk_refl(type_checker & tc, expr const & a) {
    expr A    = tc.whnf(tc.infer(a).first).first;
    level lvl = sort_level(tc.ensure_type(A).first);
    return mk_app(mk_constant(get_eq_refl_name(), {lvl}), A, a);
}

expr mk_symm(type_checker & tc, expr const & H) {
    expr p    = tc.whnf(tc.infer(H).first).first;
    lean_assert(is_eq(p));
    expr lhs  = app_arg(app_fn(p));
    expr rhs  = app_arg(p);
    expr A    = tc.infer(lhs).first;
    level lvl = sort_level(tc.ensure_type(A).first);
    return mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, lhs, rhs, H);
}

expr mk_trans(type_checker & tc, expr const & H1, expr const & H2) {
    expr p1    = tc.whnf(tc.infer(H1).first).first;
    expr p2    = tc.whnf(tc.infer(H2).first).first;
    lean_assert(is_eq(p1) && is_eq(p2));
    expr lhs1  = app_arg(app_fn(p1));
    expr rhs1  = app_arg(p1);
    expr rhs2  = app_arg(p2);
    expr A     = tc.infer(lhs1).first;
    level lvl  = sort_level(tc.ensure_type(A).first);
    return mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, lhs1, rhs1, rhs2, H1, H2});
}

expr mk_subst(type_checker & tc, expr const & motive, expr const & x, expr const & y, expr const & xeqy, expr const & h) {
    expr A    = tc.infer(x).first;
    level l1  = sort_level(tc.ensure_type(A).first);
    expr r;
    if (is_standard(tc.env())) {
        r = mk_constant(get_eq_subst_name(), {l1});
    } else {
        level l2 = sort_level(tc.ensure_type(tc.infer(h).first).first);
        r = mk_constant(get_eq_subst_name(), {l1, l2});
    }
    return mk_app({r, A, x, y, motive, xeqy, h});
}

expr mk_subst(type_checker & tc, expr const & motive, expr const & xeqy, expr const & h) {
    expr xeqy_type = tc.whnf(tc.infer(xeqy).first).first;
    return mk_subst(tc, motive, app_arg(app_fn(xeqy_type)), app_arg(xeqy_type), xeqy, h);
}

expr mk_subsingleton_elim(type_checker & tc, expr const & h, expr const & x, expr const & y) {
    expr A  = tc.infer(x).first;
    level l = sort_level(tc.ensure_type(A).first);
    expr r;
    if (is_standard(tc.env())) {
        r = mk_constant(get_subsingleton_elim_name(), {l});
    } else {
        r = mk_constant(get_is_trunc_is_hprop_elim_name(), {l});
    }
    return mk_app({r, A, h, x, y});
}

expr mk_heq(type_checker & tc, expr const & lhs, expr const & rhs) {
    expr A    = tc.whnf(tc.infer(lhs).first).first;
    expr B    = tc.whnf(tc.infer(rhs).first).first;
    level lvl = sort_level(tc.ensure_type(A).first);
    return mk_app(mk_constant(get_heq_name(), {lvl}), A, lhs, B, rhs);
}

bool is_eq_rec(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_eq_rec_name();
}

bool is_eq(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_eq_name();
}

bool is_eq(expr const & e, expr & lhs, expr & rhs) {
    if (!is_eq(e) || !is_app(app_fn(e)))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq_a_a(expr const & e) {
    if (!is_eq(e))
        return false;
    buffer<expr> args;
    get_app_args(e, args);
    return args.size() == 3 && args[1] == args[2];
}

bool is_eq_a_a(type_checker & tc, expr const & e) {
    if (!is_eq(e))
        return false;
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() != 3)
        return false;
    pair<bool, constraint_seq> d = tc.is_def_eq(args[1], args[2]);
    return d.first && !d.second;
}

bool is_heq(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_heq_name();
}

bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs) {
    if (is_heq(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        if (args.size() != 4)
            return false;
        A = args[0]; lhs = args[1]; B = args[2]; rhs = args[3];
        return true;
    } else {
        return false;
    }
}

void mk_telescopic_eq(type_checker & tc, buffer<expr> const & t, buffer<expr> const & s, buffer<expr> & eqs) {
    lean_assert(t.size() == s.size());
    lean_assert(std::all_of(s.begin(), s.end(), is_local));
    lean_assert(inductive::has_dep_elim(tc.env(), get_eq_name()));
    buffer<buffer<expr>> t_aux;
    name e_name("e");
    for (unsigned i = 0; i < t.size(); i++) {
        expr s_i = s[i];
        expr s_i_ty   = mlocal_type(s_i);
        expr s_i_ty_a = abstract_locals(s_i_ty, i, s.data());
        expr t_i = t[i];
        t_aux.push_back(buffer<expr>());
        t_aux.back().push_back(t_i);
        for (unsigned j = 0; j < i; j++) {
            if (depends_on(s_i_ty, s[j])) {
                // we need to "cast"
                buffer<expr> ty_inst_args;
                for (unsigned k = 0; k <= j; k++)
                    ty_inst_args.push_back(s[k]);
                for (unsigned k = j + 1; k < i; k++)
                    ty_inst_args.push_back(t_aux[k][j+1]);
                lean_assert(ty_inst_args.size() == i);
                expr s_i_ty = instantiate_rev(s_i_ty_a, i, ty_inst_args.data());
                buffer<expr> rec_args;
                rec_args.push_back(mlocal_type(s[j]));
                rec_args.push_back(t_aux[j][j]);
                rec_args.push_back(Fun(s[j], Fun(eqs[j], s_i_ty))); // type former ("promise")
                rec_args.push_back(t_i); // minor premise
                rec_args.push_back(s[j]);
                rec_args.push_back(eqs[j]);
                level rec_l1 = sort_level(tc.ensure_type(s_i_ty).first);
                level rec_l2 = sort_level(tc.ensure_type(mlocal_type(s[j])).first);
                t_i = mk_app(mk_constant(get_eq_rec_name(), {rec_l1, rec_l2}), rec_args.size(), rec_args.data());
            }
            t_aux.back().push_back(t_i);
        }
        expr eq = mk_local(tc.mk_fresh_name(), e_name.append_after(i+1), mk_eq(tc, t_i, s_i), binder_info());
        eqs.push_back(eq);
    }
}

void mk_telescopic_eq(type_checker & tc, buffer<expr> const & t, buffer<expr> & eqs) {
    lean_assert(std::all_of(t.begin(), t.end(), is_local));
    lean_assert(inductive::has_dep_elim(tc.env(), get_eq_name()));
    buffer<expr> s;
    for (unsigned i = 0; i < t.size(); i++) {
        expr ty = mlocal_type(t[i]);
        ty = abstract_locals(ty, i, t.data());
        ty = instantiate_rev(ty, i, s.data());
        expr local = mk_local(tc.mk_fresh_name(), local_pp_name(t[i]).append_after("'"), ty, local_info(t[i]));
        s.push_back(local);
    }
    return mk_telescopic_eq(tc, t, s, eqs);
}

level mk_max(levels const & ls) {
    if (!ls)
        return mk_level_zero();
    else if (!tail(ls))
        return head(ls);
    else
        return mk_max(head(ls), mk_max(tail(ls)));
}

expr telescope_to_sigma(type_checker & tc, unsigned sz, expr const * ts, constraint_seq & cs) {
    lean_assert(sz > 0);
    unsigned i = sz - 1;
    expr r = mlocal_type(ts[i]);
    while (i > 0) {
        --i;
        expr const & a  = ts[i];
        expr const & A  = mlocal_type(a);
        expr const & Ba = r;
        level l1        = sort_level(tc.ensure_type(A, cs));
        level l2        = sort_level(tc.ensure_type(Ba, cs));
        r = mk_app(mk_constant(get_sigma_name(), {l1, l2}), A, Fun(a, Ba));
    }
    return r;
}

expr mk_sigma_mk(type_checker & tc, unsigned sz, expr const * ts, expr const * as, constraint_seq & cs) {
    lean_assert(sz > 0);
    if (sz == 1)
        return as[0];
    buffer<expr> new_ts;
    for (unsigned i = 1; i < sz; i++)
        new_ts.push_back(instantiate(abstract_local(ts[i], ts[0]), as[0]));
    expr arg1      = mlocal_type(ts[0]);
    expr arg2_core = telescope_to_sigma(tc, sz-1, ts+1, cs);
    expr arg2      = Fun(ts[0], arg2_core);
    expr arg3      = as[0];
    expr arg4      = mk_sigma_mk(tc, sz-1, new_ts.data(), as+1, cs);
    level l1       = sort_level(tc.ensure_type(arg1, cs));
    level l2       = sort_level(tc.ensure_type(arg2_core, cs));
    return mk_app(mk_constant(get_sigma_mk_name(), {l1, l2}), arg1, arg2, arg3, arg4);
}

expr mk_sigma_mk(type_checker & tc, buffer<expr> const & ts, buffer<expr> const & as, constraint_seq & cs) {
    lean_assert(ts.size() == as.size());
    return mk_sigma_mk(tc, ts.size(), ts.data(), as.data(), cs);
}

bool is_none(expr const & e, expr & A) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_constant(fn) && const_name(fn) == get_option_none_name() && args.size() == 1) {
        A = args[0];
        return true;
    } else {
        return false;
    }
}

bool is_some(expr const & e, expr & A, expr & a) {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (is_constant(fn) && const_name(fn) == get_option_some_name() && args.size() == 2) {
        A = args[0];
        a = args[1];
        return true;
    } else {
        return false;
    }
}

expr infer_implicit_params(expr const & type, unsigned nparams, implicit_infer_kind k) {
    switch (k) {
    case implicit_infer_kind::Implicit: {
        bool strict = true;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::RelaxedImplicit: {
        bool strict = false;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::None:
        return type;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool has_expr_metavar_relaxed(expr const & e) {
    if (!has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e))
                return false;
            if (is_metavar(e)) {
                found = true;
                return false;
            }
            if (is_local(e))
                return false; // do not visit type
            return true;
        });
    return found;
}

constraint instantiate_metavars(constraint const & c, substitution & s) {
    switch (c.kind()) {
    case constraint_kind::Eq:
        return mk_eq_cnstr(s.instantiate_all(cnstr_lhs_expr(c)),
                           s.instantiate_all(cnstr_rhs_expr(c)),
                           c.get_justification());
    case constraint_kind::LevelEq:
        return mk_level_eq_cnstr(s.instantiate(cnstr_lhs_level(c)), s.instantiate(cnstr_rhs_level(c)), c.get_justification());
    case constraint_kind::Choice: {
        expr m = cnstr_expr(c);
        lean_assert(is_meta(m));
        buffer<expr> args;
        expr mvar = get_app_args(m, args);
        mvar = update_mlocal(mvar, s.instantiate_all(mlocal_type(mvar)));
        for (expr & arg : args)
            arg = s.instantiate_all(arg);
        return mk_choice_cnstr(mk_app(mvar, args),
                               cnstr_choice_fn(c),
                               cnstr_delay_factor_core(c),
                               cnstr_is_owner(c), c.get_justification());
    }}
    lean_unreachable(); // LCOV_EXCL_LINE
}

void check_term(type_checker & tc, expr const & e) {
    expr tmp = unfold_untrusted_macros(tc.env(), e);
    tc.check_ignore_undefined_universes(tmp);
}

void check_term(environment const & env, expr const & e) {
    expr tmp = unfold_untrusted_macros(env, e);
    type_checker(env).check_ignore_undefined_universes(tmp);
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

justification mk_type_mismatch_jst(expr const & v, expr const & v_type, expr const & t, expr const & src) {
    return mk_justification(src, [=](formatter const & fmt, substitution const & subst, bool) {
            substitution s(subst);
            return pp_type_mismatch(fmt, s.instantiate(v), s.instantiate(v_type), s.instantiate(t));
        });
}

format format_goal(formatter const & _fmt, buffer<expr> const & hyps, expr const & conclusion, substitution const & s) {
    substitution tmp_subst(s);
    options opts     = _fmt.get_options();
    opts             = opts.update_if_undef(get_pp_purify_locals_name(), false);
    formatter fmt    = _fmt.update_options(opts);
    unsigned indent  = get_pp_indent(opts);
    bool unicode     = get_pp_unicode(opts);
    bool compact     = get_pp_compact_goals(opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    format r;
    unsigned i = hyps.size();
    bool first = true;
    while (i > 0) {
        i--;
        expr l     = hyps[i];
        format ids = fmt(l);
        expr t     = tmp_subst.instantiate(mlocal_type(l));
        lean_assert(hyps.size() > 0);
        while (i > 0) {
            expr l2 = hyps[i-1];
            expr t2 = tmp_subst.instantiate(mlocal_type(l2));
            if (t2 != t)
                break;
            ids = fmt(l2) + space() + ids;
            i--;
        }
        if (first)
            first = false;
        else
            r = compose(comma(), line()) + r;
        r = group(ids + space() + colon() + nest(indent, line() + fmt(t))) + r;
    }
    if (compact)
        r = group(r);
    r += line() + turnstile + space() + nest(indent, fmt(tmp_subst.instantiate(conclusion)));
    if (compact)
        r = group(r);
    return r;
}

pair<expr, justification> update_meta(expr const & meta, substitution s) {
    buffer<expr> args;
    expr mvar = get_app_args(meta, args);
    justification j;
    auto p = s.instantiate_metavars(mlocal_type(mvar));
    mvar   = update_mlocal(mvar, p.first);
    j      = p.second;
    for (expr & arg : args) {
        auto p = s.instantiate_metavars(mlocal_type(arg));
        arg    = update_mlocal(arg, p.first);
        j      = mk_composite1(j, p.second);
    }
    return mk_pair(mk_app(mvar, args), j);
}

expr instantiate_meta(expr const & meta, substitution & subst) {
    lean_assert(is_meta(meta));
    buffer<expr> locals;
    expr mvar = get_app_args(meta, locals);
    mvar = update_mlocal(mvar, subst.instantiate_all(mlocal_type(mvar)));
    for (auto & local : locals)
        local = subst.instantiate_all(local);
    return mk_app(mvar, locals);
}

justification mk_failed_to_synthesize_jst(environment const & env, expr const & m) {
    return mk_justification(m, [=](formatter const & fmt, substitution const & subst, bool) {
            substitution tmp(subst);
            expr new_m    = instantiate_meta(m, tmp);
            expr new_type = type_checker(env).infer(new_m).first;
            buffer<expr> hyps;
            get_app_args(new_m, hyps);
            return format("failed to synthesize placeholder") + line() + format_goal(fmt, hyps, new_type, subst);
        });
}

type_checker_ptr mk_type_checker(environment const & env, name_generator && ngen, name_predicate const & pred) {
    return std::unique_ptr<type_checker>(new type_checker(env, std::move(ngen),
                                         std::unique_ptr<converter>(new hint_converter<projection_converter>(env, pred))));
}

type_checker_ptr mk_simple_type_checker(environment const & env, name_generator && ngen, name_predicate const & pred) {
    return std::unique_ptr<type_checker>(new type_checker(env, std::move(ngen),
                                         std::unique_ptr<converter>(new hint_converter<default_converter>(env, pred))));
}
}

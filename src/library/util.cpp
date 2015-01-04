/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/locals.h"

namespace lean {
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

bool has_lift_decls(environment const & env) {
    return has_constructor(env, name{"lift", "up"}, "lift", 2);
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
    type = tc.whnf(type, cs);
    while (is_pi(type)) {
        expr local;
        if (binfo)
            local = mk_local(tc.mk_fresh_name(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(tc.mk_fresh_name(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type = tc.whnf(instantiate(binding_body(type), local), cs);
    }
    return type;
}

expr to_telescope(type_checker & tc, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    constraint_seq cs;
    return to_telescope(tc, type, telescope, binfo, cs);
}

static expr * g_true = nullptr;
static expr * g_true_intro = nullptr;
static expr * g_and = nullptr;
static expr * g_and_intro = nullptr;
static expr * g_and_elim_left = nullptr;
static expr * g_and_elim_right = nullptr;

static name * g_unit_name = nullptr;
static name * g_unit_mk_name = nullptr;
static name * g_prod_name = nullptr;
static name * g_prod_mk_name = nullptr;
static name * g_pr1_name = nullptr;
static name * g_pr2_name = nullptr;

static name * g_eq_name = nullptr;
static name * g_eq_refl_name = nullptr;
static name * g_eq_rec_name = nullptr;

static name * g_heq_name = nullptr;

static name * g_sigma_name = nullptr;
static name * g_sigma_mk_name = nullptr;

void initialize_library_util() {
    g_true           = new expr(mk_constant("true"));
    g_true_intro     = new expr(mk_constant(name({"true", "intro"})));
    g_and            = new expr(mk_constant("and"));
    g_and_intro      = new expr(mk_constant(name({"and", "intro"})));
    g_and_elim_left  = new expr(mk_constant(name({"and", "elim_left"})));
    g_and_elim_right = new expr(mk_constant(name({"and", "elim_right"})));

    g_unit_name      = new name("unit");
    g_unit_mk_name   = new name{"unit", "star"};
    g_prod_name      = new name("prod");
    g_prod_mk_name   = new name{"prod", "mk"};
    g_pr1_name       = new name{"prod", "pr1"};
    g_pr2_name       = new name{"prod", "pr2"};

    g_eq_name        = new name("eq");
    g_eq_refl_name   = new name{"eq", "refl"};
    g_eq_rec_name    = new name{"eq", "rec"};

    g_heq_name       = new name("heq");

    g_sigma_name     = new name("sigma");
    g_sigma_mk_name  = new name{"sigma", "mk"};
}

void finalize_library_util() {
    delete g_true;
    delete g_true_intro;
    delete g_and;
    delete g_and_intro;
    delete g_and_elim_left;
    delete g_and_elim_right;
    delete g_unit_name;
    delete g_unit_mk_name;
    delete g_prod_name;
    delete g_prod_mk_name;
    delete g_pr1_name;
    delete g_pr2_name;
    delete g_eq_name;
    delete g_eq_refl_name;
    delete g_eq_rec_name;
    delete g_heq_name;
    delete g_sigma_name;
    delete g_sigma_mk_name;
}

expr mk_true() {
    return *g_true;
}

expr mk_true_intro() {
    return *g_true_intro;
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
    return mk_constant(*g_unit_name, {l});
}

expr mk_unit_mk(level const & l) {
    return mk_constant(*g_unit_mk_name, {l});
}

expr mk_prod(type_checker & tc, expr const & A, expr const & B) {
    level l1 = sort_level(tc.ensure_type(A).first);
    level l2 = sort_level(tc.ensure_type(B).first);
    return mk_app(mk_constant(*g_prod_name, {l1, l2}), A, B);
}

expr mk_pair(type_checker & tc, expr const & a, expr const & b) {
    expr A = tc.infer(a).first;
    expr B = tc.infer(b).first;
    level l1 = sort_level(tc.ensure_type(A).first);
    level l2 = sort_level(tc.ensure_type(B).first);
    return mk_app(mk_constant(*g_prod_mk_name, {l1, l2}), A, B, a, b);
}

expr mk_pr1(type_checker & tc, expr const & p) {
    expr AxB = tc.whnf(tc.infer(p).first).first;
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(*g_pr1_name, const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_pr2(type_checker & tc, expr const & p) {
    expr AxB = tc.whnf(tc.infer(p).first).first;
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(*g_pr2_name, const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_unit(level const & l, bool prop) { return prop ? mk_true() : mk_unit(l); }
expr mk_unit_mk(level const & l, bool prop) { return prop ? mk_true_intro() : mk_unit_mk(l); }
expr mk_prod(type_checker & tc, expr const & a, expr const & b, bool prop) { return prop ? mk_and(a, b) : mk_prod(tc, a, b); }
expr mk_pair(type_checker & tc, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and_intro(tc, a, b) : mk_pair(tc, a, b);
}
expr mk_pr1(type_checker & tc, expr const & p, bool prop) { return prop ? mk_and_elim_left(tc, p) : mk_pr1(tc, p); }
expr mk_pr2(type_checker & tc, expr const & p, bool prop) { return prop ? mk_and_elim_right(tc, p) : mk_pr2(tc, p); }

expr mk_eq(type_checker & tc, expr const & lhs, expr const & rhs) {
    expr A    = tc.whnf(tc.infer(lhs).first).first;
    level lvl = sort_level(tc.ensure_type(A).first);
    return mk_app(mk_constant(*g_eq_name, {lvl}), A, lhs, rhs);
}

expr mk_refl(type_checker & tc, expr const & a) {
    expr A    = tc.whnf(tc.infer(a).first).first;
    level lvl = sort_level(tc.ensure_type(A).first);
    return mk_app(mk_constant(*g_eq_refl_name, {lvl}), A, a);
}

expr mk_heq(type_checker & tc, expr const & lhs, expr const & rhs) {
    expr A    = tc.whnf(tc.infer(lhs).first).first;
    expr B    = tc.whnf(tc.infer(rhs).first).first;
    level lvl = sort_level(tc.ensure_type(A).first);
    return mk_app(mk_constant(*g_heq_name, {lvl}), A, lhs, B, rhs);
}

bool is_eq_rec(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == *g_eq_rec_name;
}

bool is_eq(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == *g_eq_name;
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

void mk_telescopic_eq(type_checker & tc, buffer<expr> const & t, buffer<expr> const & s, buffer<expr> & eqs) {
    lean_assert(t.size() == s.size());
    lean_assert(std::all_of(s.begin(), s.end(), is_local));
    lean_assert(inductive::has_dep_elim(tc.env(), *g_eq_name));
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
                t_i = mk_app(mk_constant(*g_eq_rec_name, {rec_l1, rec_l2}), rec_args.size(), rec_args.data());
            }
            t_aux.back().push_back(t_i);
        }
        expr eq = mk_local(tc.mk_fresh_name(), e_name.append_after(i+1), mk_eq(tc, t_i, s_i), binder_info());
        eqs.push_back(eq);
    }
}

void mk_telescopic_eq(type_checker & tc, buffer<expr> const & t, buffer<expr> & eqs) {
    lean_assert(std::all_of(t.begin(), t.end(), is_local));
    lean_assert(inductive::has_dep_elim(tc.env(), *g_eq_name));
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
        r = mk_app(mk_constant(*g_sigma_name, {l1, l2}), A, Fun(a, Ba));
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
    return mk_app(mk_constant(*g_sigma_mk_name, {l1, l2}), arg1, arg2, arg3, arg4);
}

expr mk_sigma_mk(type_checker & tc, buffer<expr> const & ts, buffer<expr> const & as, constraint_seq & cs) {
    lean_assert(ts.size() == as.size());
    return mk_sigma_mk(tc, ts.size(), ts.data(), as.data(), cs);
}

}

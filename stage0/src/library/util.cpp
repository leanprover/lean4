/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include <lean/version.h>
#include "runtime/option_ref.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/inductive.h"
#include "library/util.h"
#include "library/suffixes.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/projection.h"
#include "library/replace_visitor.h"
#include "library/num.h"
#include "githash.h" // NOLINT

namespace lean {
name mk_unused_name(environment const & env, name const & n, unsigned & idx) {
    name curr = n;
    while (true) {
        if (!env.find(curr))
            return curr;
        curr = n.append_after(idx);
        idx++;
    }
}

name mk_unused_name(environment const & env, name const & n) {
    unsigned idx = 1;
    return mk_unused_name(env, n, idx);
}

/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type) {
    unsigned r = 0;
    while (is_pi(type)) {
        type = binding_body(type);
        r++;
    }
    return r;
}

optional<expr> is_optional_param(expr const & e) {
    if (is_app_of(e, get_opt_param_name(), 2)) {
        return some_expr(app_arg(e));
    } else {
        return none_expr();
    }
}

optional<expr_pair> is_auto_param(expr const & e) {
    if (is_app_of(e, get_auto_param_name(), 2)) {
        return optional<expr_pair>(app_arg(app_fn(e)), app_arg(e));
    } else {
        return optional<expr_pair>();
    }
}

name mk_fresh_lp_name(names const & lp_names) {
    name l("l");
    int i = 1;
    while (std::find(lp_names.begin(), lp_names.end(), l) != lp_names.end()) {
        l = name("l").append_after(i);
        i++;
    }
    return l;
}

bool occurs(expr const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return n == e; }));
}

bool occurs(name const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; }));
}

bool is_app_of(expr const & t, name const & f_name) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name;
}

bool is_app_of(expr const & t, name const & f_name, unsigned nargs) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name && get_app_num_args(t) == nargs;
}

expr consume_auto_opt_param(expr const & type) {
    if (is_app_of(type, get_auto_param_name(), 2) || is_app_of(type, get_opt_param_name(), 2)) {
        return app_arg(app_fn(type));
    } else {
        return type;
    }
}

optional<expr> unfold_term(environment const & env, expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->has_value())
        return none_expr();
    expr d = instantiate_value_lparams(*decl, const_levels(f));
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
    case level_kind::Zero: case level_kind::Param: case level_kind::MVar:
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
    if (!d || d->has_value())
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

bool has_punit_decls(environment const & env) {
    return has_constructor(env, get_punit_unit_name(), get_punit_name(), 0);
}

bool has_eq_decls(environment const & env) {
    return has_constructor(env, get_eq_refl_name(), get_eq_name(), 2);
}

bool has_heq_decls(environment const & env) {
    return has_constructor(env, get_heq_refl_name(), get_heq_name(), 2);
}

bool has_pprod_decls(environment const & env) {
    return has_constructor(env, get_pprod_mk_name(), get_pprod_name(), 4);
}

bool has_and_decls(environment const & env) {
    return has_constructor(env, get_and_intro_name(), get_and_name(), 4);
}

static name * g_util_fresh = nullptr;

level get_datatype_level(environment const & env, expr const & ind_type) {
    local_ctx lctx;
    name_generator ngen(*g_util_fresh);
    expr it = type_checker(env, lctx).whnf(ind_type);
    while (is_pi(it)) {
        expr local = lctx.mk_local_decl(ngen, binding_name(it), binding_domain(it), binding_info(it));
        it = type_checker(env, lctx).whnf(instantiate(binding_body(it), local));
    }
    if (is_sort(it)) {
        return sort_level(it);
    } else {
        throw exception("invalid inductive datatype type");
    }
}

expr update_result_sort(expr t, level const & l) {
    if (is_pi(t)) {
        return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
    } else if (is_sort(t)) {
        return update_sort(t, l);
    } else {
        lean_unreachable();
    }
}

bool is_inductive_predicate(environment const & env, name const & n) {
    constant_info info = env.get(n);
    if (!info.is_inductive())
        return false;
    return is_zero(get_datatype_level(env, env.get(n).get_type()));
}

bool can_elim_to_type(environment const & env, name const & n) {
    constant_info ind_info = env.get(n);
    if (!ind_info.is_inductive()) return false;
    constant_info rec_info = env.get(mk_rec_name(n));
    return rec_info.get_num_lparams() > ind_info.get_num_lparams();
}

void get_constructor_names(environment const & env, name const & n, buffer<name> & result) {
    constant_info info = env.get(n);
    if (!info.is_inductive()) return;
    to_buffer(info.to_inductive_val().get_cnstrs(), result);
}

optional<name> is_constructor_app_ext(environment const & env, expr const & e) {
    if (auto r = is_constructor_app(env, e))
        return r;
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return optional<name>();
    optional<constant_info> info = env.find(const_name(f));
    if (!info || !info->has_value())
        return optional<name>();
    expr val = info->get_value();
    expr const * it = &val;
    while (is_lambda(*it))
        it = &binding_body(*it);
    return is_constructor_app_ext(env, *it);
}

void get_constructor_relevant_fields(environment const & env, name const & n, buffer<bool> & result) {
    constant_info info  = env.get(n);
    lean_assert(info.is_constructor());
    constructor_val val = info.to_constructor_val();
    expr type           = info.get_type();
    name I_name         = val.get_induct();
    unsigned nparams    = val.get_nparams();
    local_ctx lctx;
    name_generator ngen(*g_util_fresh);
    buffer<expr> telescope;
    to_telescope(env, lctx, ngen, type, telescope);
    lean_assert(telescope.size() >= nparams);
    for (unsigned i = nparams; i < telescope.size(); i++) {
        expr ftype = lctx.get_type(telescope[i]);
        if (type_checker(env, lctx).is_prop(ftype)) {
            result.push_back(false);
        } else {
            buffer<expr> tmp;
            expr n_ftype = to_telescope(env, lctx, ngen, ftype, tmp);
            result.push_back(!is_sort(n_ftype) && !type_checker(env, lctx).is_prop(n_ftype));
        }
    }
}

unsigned get_num_constructors(environment const & env, name const & n) {
    constant_info info = env.get(n);
    lean_assert(info.is_inductive());
    return length(info.to_inductive_val().get_cnstrs());
}

unsigned get_constructor_idx(environment const & env, name const & n) {
    constant_info info  = env.get(n);
    lean_assert(info.is_constructor());
    constructor_val val = info.to_constructor_val();
    name I_name         = val.get_induct();
    buffer<name> cnames;
    get_constructor_names(env, I_name, cnames);
    unsigned r  = 0;
    for (name const & cname : cnames) {
        if (cname == n)
            return r;
        r++;
    }
    lean_unreachable();
}

name get_constructor_inductive_type(environment const & env, name const & ctor_name) {
    constant_info info  = env.get(ctor_name);
    lean_assert(info.is_constructor());
    constructor_val val = info.to_constructor_val();
    return val.get_induct();
}

expr instantiate_lparam(expr const & e, name const & p, level const & l) {
    return instantiate_lparams(e, names(p), levels(l));
}

expr to_telescope(bool pi, local_ctx & lctx, name_generator & ngen, expr e, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    while ((pi && is_pi(e)) || (!pi && is_lambda(e))) {
        expr local;
        if (binfo)
            local = lctx.mk_local_decl(ngen, binding_name(e), binding_domain(e), *binfo);
        else
            local = lctx.mk_local_decl(ngen, binding_name(e), binding_domain(e), binding_info(e));
        telescope.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    return e;
}

expr to_telescope(local_ctx & lctx, name_generator & ngen, expr const & type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    return to_telescope(true, lctx, ngen, type, telescope, binfo);
}

expr to_telescope(environment const & env, local_ctx & lctx, name_generator & ngen, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    expr new_type = type_checker(env, lctx).whnf(type);
    while (is_pi(new_type)) {
        type = new_type;
        expr local;
        if (binfo)
            local = lctx.mk_local_decl(ngen, binding_name(type), binding_domain(type), *binfo);
        else
            local = lctx.mk_local_decl(ngen, binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type     = instantiate(binding_body(type), local);
        new_type = type_checker(env, lctx).whnf(type);
    }
    return type;
}

/* ----------------------------------------------

   Helper functions for creating basic operations

   ---------------------------------------------- */
static expr * g_true = nullptr;
static expr * g_true_intro = nullptr;
static expr * g_and = nullptr;
static expr * g_and_intro = nullptr;
static expr * g_and_left = nullptr;
static expr * g_and_right = nullptr;

expr mk_true() {
    return *g_true;
}

bool is_true(expr const & e) {
    return e == *g_true;
}

expr mk_true_intro() {
    return *g_true_intro;
}

bool is_and(expr const & e) {
    return is_app_of(e, get_and_name(), 2);
}

bool is_and(expr const & e, expr & arg1, expr & arg2) {
    if (is_and(e)) {
        arg1 = app_arg(app_fn(e));
        arg2 = app_arg(e);
        return true;
    } else {
        return false;
    }
}

expr mk_and(expr const & a, expr const & b) {
    return mk_app(*g_and, a, b);
}

expr mk_unit(level const & l) {
    return mk_constant(get_punit_name(), {l});
}

expr mk_unit_mk(level const & l) {
    return mk_constant(get_punit_unit_name(), {l});
}

static expr * g_unit = nullptr;
static expr * g_unit_mk = nullptr;

expr mk_unit() {
    return *g_unit;
}

expr mk_unit_mk() {
    return *g_unit_mk;
}

static expr * g_nat         = nullptr;
static expr * g_nat_zero    = nullptr;
static expr * g_nat_one     = nullptr;
static expr * g_nat_bit0_fn = nullptr;
static expr * g_nat_bit1_fn = nullptr;
static expr * g_nat_add_fn  = nullptr;

static void initialize_nat() {
    g_nat            = new expr(mk_constant(get_nat_name()));
    mark_persistent(g_nat->raw());
    g_nat_zero       = new expr(mk_app(mk_constant(get_has_zero_zero_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_zero_name())}));
    mark_persistent(g_nat_zero->raw());
    g_nat_one        = new expr(mk_app(mk_constant(get_has_one_one_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name())}));
    mark_persistent(g_nat_one->raw());
    g_nat_bit0_fn    = new expr(mk_app(mk_constant(get_bit0_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_add_name())}));
    mark_persistent(g_nat_bit0_fn->raw());
    g_nat_bit1_fn    = new expr(mk_app(mk_constant(get_bit1_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name()), mk_constant(get_nat_has_add_name())}));
    mark_persistent(g_nat_bit1_fn->raw());
    g_nat_add_fn     = new expr(mk_app(mk_constant(get_has_add_add_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_add_name())}));
    mark_persistent(g_nat_add_fn->raw());
}

static void finalize_nat() {
    delete g_nat;
    delete g_nat_zero;
    delete g_nat_one;
    delete g_nat_bit0_fn;
    delete g_nat_bit1_fn;
    delete g_nat_add_fn;
}

expr mk_nat_type() { return *g_nat; }
bool is_nat_type(expr const & e) { return e == *g_nat; }
expr mk_nat_zero() { return *g_nat_zero; }
expr mk_nat_one() { return *g_nat_one; }
expr mk_nat_bit0(expr const & e) { return mk_app(*g_nat_bit0_fn, e); }
expr mk_nat_bit1(expr const & e) { return mk_app(*g_nat_bit1_fn, e); }
expr mk_nat_add(expr const & e1, expr const & e2) { return mk_app(*g_nat_add_fn, e1, e2); }

static expr * g_int = nullptr;

static void initialize_int() {
    g_int = new expr(mk_constant(get_int_name()));
    mark_persistent(g_int->raw());
}

static void finalize_int() {
    delete g_int;
}

expr mk_int_type() { return *g_int; }
bool is_int_type(expr const & e) { return e == *g_int; }

static expr * g_char = nullptr;

expr mk_char_type() { return *g_char; }

static void initialize_char() {
    g_char = new expr(mk_constant(get_char_name()));
    mark_persistent(g_char->raw());
}

static void finalize_char() {
    delete g_char;
}

expr mk_unit(level const & l, bool prop) { return prop ? mk_true() : mk_unit(l); }
expr mk_unit_mk(level const & l, bool prop) { return prop ? mk_true_intro() : mk_unit_mk(l); }

bool is_ite(expr const & e) {
    return is_app_of(e, get_ite_name(), 5);
}

bool is_ite(expr const & e, expr & c, expr & H, expr & A, expr & t, expr & f) {
    if (is_ite(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(args.size() == 5);
        c = args[0]; H = args[1]; A = args[2]; t = args[3]; f = args[4];
        return true;
    } else {
        return false;
    }
}

bool is_iff(expr const & e) {
    return is_app_of(e, get_iff_name(), 2);
}

bool is_iff(expr const & e, expr & lhs, expr & rhs) {
    if (!is_iff(e))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}
expr mk_iff(expr const & lhs, expr const & rhs) {
    return mk_app(mk_constant(get_iff_name()), lhs, rhs);
}
expr mk_iff_refl(expr const & a) {
    return mk_app(mk_constant(get_iff_refl_name()), a);
}
expr mk_propext(expr const & lhs, expr const & rhs, expr const & iff_pr) {
    return mk_app(mk_constant(get_propext_name()), lhs, rhs, iff_pr);
}

bool is_eq_ndrec_core(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_eq_ndrec_name();
}

bool is_eq_ndrec(expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return const_name(fn) == get_eq_ndrec_name();
}

bool is_eq_rec(expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return const_name(fn) == get_eq_rec_name();
}

bool is_eq(expr const & e) {
    return is_app_of(e, get_eq_name(), 3);
}

bool is_eq(expr const & e, expr & lhs, expr & rhs) {
    if (!is_eq(e))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq(expr const & e, expr & A, expr & lhs, expr & rhs) {
    if (!is_eq(e))
        return false;
    A   = app_arg(app_fn(app_fn(e)));
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq_a_a(expr const & e) {
    if (!is_eq(e))
        return false;
    expr lhs = app_arg(app_fn(e));
    expr rhs = app_arg(e);
    return lhs == rhs;
}

bool is_heq(expr const & e) {
    return is_app_of(e, get_heq_name(), 4);
}

bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs) {
    if (is_heq(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(args.size() == 4);
        A = args[0]; lhs = args[1]; B = args[2]; rhs = args[3];
        return true;
    } else {
        return false;
    }
}

bool is_heq(expr const & e, expr & lhs, expr & rhs) {
    expr A, B;
    return is_heq(e, A, lhs, B, rhs);
}

expr mk_false() {
    return mk_constant(get_false_name());
}

expr mk_empty() {
    return mk_constant(get_empty_name());
}

bool is_false(expr const & e) {
    return is_constant(e) && const_name(e) == get_false_name();
}

bool is_empty(expr const & e) {
    return is_constant(e) && const_name(e) == get_empty_name();
}

bool is_or(expr const & e) {
    return is_app_of(e, get_or_name(), 2);
}

bool is_or(expr const & e, expr & A, expr & B) {
    if (is_or(e)) {
        A = app_arg(app_fn(e));
        B = app_arg(e);
        return true;
    } else {
        return false;
    }
}

bool is_not(expr const & e, expr & a) {
    if (is_app_of(e, get_not_name(), 1)) {
        a = app_arg(e);
        return true;
    } else if (is_pi(e) && is_false(binding_body(e))) {
        a = binding_domain(e);
        return true;
    } else {
        return false;
    }
}

bool is_not_or_ne(expr const & e, expr & a) {
    if (is_not(e, a)) {
        return true;
    } else if (is_app_of(e, get_ne_name(), 3)) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        expr new_fn     = mk_constant(get_eq_name(), const_levels(fn));
        a               = mk_app(new_fn, args);
        return true;
    } else {
        return false;
    }
}

expr mk_not(expr const & e) {
    return mk_app(mk_constant(get_not_name()), e);
}

bool is_exists(expr const & e, expr & A, expr & p) {
    if (is_app_of(e, get_exists_name(), 2)) {
        A = app_arg(app_fn(e));
        p = app_arg(e);
        return true;
    } else {
        return false;
    }
}

bool is_exists(expr const & e) {
    return is_app_of(e, get_exists_name(), 2);
}

optional<expr> get_binary_op(expr const & e) {
    if (!is_app(e) || !is_app(app_fn(e)))
        return none_expr();
    return some_expr(app_fn(app_fn(e)));
}

optional<expr> get_binary_op(expr const & e, expr & arg1, expr & arg2) {
    if (auto op = get_binary_op(e)) {
        arg1 = app_arg(app_fn(e));
        arg2 = app_arg(e);
        return some_expr(*op);
    } else {
        return none_expr();
    }
}

expr mk_nary_app(expr const & op, buffer<expr> const & nary_args) {
    return mk_nary_app(op, nary_args.size(), nary_args.data());
}

expr mk_nary_app(expr const & op, unsigned num_nary_args, expr const * nary_args) {
    lean_assert(num_nary_args >= 2);
    // f x1 x2 x3 ==> f x1 (f x2 x3)
    expr e = mk_app(op, nary_args[num_nary_args - 2], nary_args[num_nary_args - 1]);
    for (int i = num_nary_args - 3; i >= 0; --i) {
        e = mk_app(op, nary_args[i], e);
    }
    return e;
}

bool is_annotated_lamba(expr const & e) {
    return
        is_lambda(e) ||
        (is_annotation(e) && is_lambda(get_nested_annotation_arg(e)));
}

bool is_annotated_head_beta(expr const & t) {
    return is_app(t) && is_annotated_lamba(get_app_fn(t));
}

expr annotated_head_beta_reduce(expr const & t) {
    if (!is_annotated_head_beta(t)) {
        return t;
    } else {
        buffer<expr> args;
        expr f = get_app_rev_args(t, args);
        if (is_annotation(f))
            f = get_nested_annotation_arg(f);
        lean_assert(is_lambda(f));
        return annotated_head_beta_reduce(apply_beta(f, args.size(), args.data()));
    }
}

expr try_eta(expr const & e) {
    if (is_lambda(e)) {
        expr const & b = binding_body(e);
        if (is_lambda(b)) {
            expr new_b = try_eta(b);
            if (is_eqp(b, new_b)) {
                return e;
            } else if (is_app(new_b) && is_var(app_arg(new_b), 0) && !has_loose_bvar(app_fn(new_b), 0)) {
                return lower_loose_bvars(app_fn(new_b), 1);
            } else {
                return update_binding(e, binding_domain(e), new_b);
            }
        } else if (is_app(b) && is_var(app_arg(b), 0) && !has_loose_bvar(app_fn(b), 0)) {
            return lower_loose_bvars(app_fn(b), 1);
        } else {
            return e;
        }
    } else {
        return e;
    }
}

template<bool Eta, bool Beta>
class eta_beta_reduce_fn : public replace_visitor {
public:
    virtual expr visit_app(expr const & e) override {
        expr e1 = replace_visitor::visit_app(e);
        if (Beta && is_head_beta(e1)) {
            return visit(head_beta_reduce(e1));
        } else {
            return e1;
        }
    }

    virtual expr visit_lambda(expr const & e) override {
        expr e1 = replace_visitor::visit_lambda(e);
        if (Eta) {
            while (true) {
                expr e2 = try_eta(e1);
                if (is_eqp(e1, e2))
                    return e1;
                else
                    e1 = e2;
            }
        } else {
            return e1;
        }
    }
};

expr beta_reduce(expr t) {
    return eta_beta_reduce_fn<false, true>()(t);
}

expr eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, false>()(t);
}

expr beta_eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, true>()(t);
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
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

static expr * g_bool = nullptr;
static expr * g_bool_true = nullptr;
static expr * g_bool_false = nullptr;

void initialize_bool() {
    g_bool = new expr(mk_constant(get_bool_name()));
    mark_persistent(g_bool->raw());
    g_bool_false = new expr(mk_constant(get_bool_false_name()));
    mark_persistent(g_bool_false->raw());
    g_bool_true = new expr(mk_constant(get_bool_true_name()));
    mark_persistent(g_bool_true->raw());
}

void finalize_bool() {
    delete g_bool;
    delete g_bool_false;
    delete g_bool_true;
}

expr mk_bool() { return *g_bool; }
expr mk_bool_true() { return *g_bool_true; }
expr mk_bool_false() { return *g_bool_false; }
expr to_bool_expr(bool b) { return b ? mk_bool_true() : mk_bool_false(); }

name get_dep_recursor(environment const &, name const & n) {
    return name(n, g_rec);
}

name get_dep_cases_on(environment const &, name const & n) {
    return name(n, g_cases_on);
}

extern "C" object * lean_mk_unsafe_rec_name(object *);
extern "C" object * lean_is_unsafe_rec_name(object *);

name mk_unsafe_rec_name(name const & n) {
    return name(lean_mk_unsafe_rec_name(n.to_obj_arg()));
}

optional<name> is_unsafe_rec_name(name const & n) {
    return option_ref<name>(lean_is_unsafe_rec_name(n.to_obj_arg())).get();
}

static std::string * g_short_version_string = nullptr;
std::string const & get_short_version_string() { return *g_short_version_string; }

static std::string * g_version_string = nullptr;
std::string const & get_version_string() { return *g_version_string; }

expr const & extract_mdata(expr const & e) {
    if (is_mdata(e)) {
        return extract_mdata(mdata_expr(e));
    } else {
        return e;
    }
}

optional<expr> to_optional_expr(obj_arg o) {
    if (is_scalar(o)) return none_expr();
    optional<expr> r = some_expr(expr(cnstr_get(o, 0), true));
    dec(o);
    return r;
}

void initialize_library_util() {
    g_unit           = new expr(mk_constant(get_unit_name()));
    mark_persistent(g_unit->raw());
    g_unit_mk        = new expr(mk_constant(get_unit_unit_name()));
    mark_persistent(g_unit_mk->raw());
    g_true           = new expr(mk_constant(get_true_name()));
    mark_persistent(g_true->raw());
    g_true_intro     = new expr(mk_constant(get_true_intro_name()));
    mark_persistent(g_true_intro->raw());
    g_and            = new expr(mk_constant(get_and_name()));
    mark_persistent(g_and->raw());
    g_and_intro      = new expr(mk_constant(get_and_intro_name()));
    mark_persistent(g_and_intro->raw());
    g_and_left  = new expr(mk_constant(get_and_left_name()));
    mark_persistent(g_and_left->raw());
    g_and_right = new expr(mk_constant(get_and_right_name()));
    mark_persistent(g_and_right->raw());
    initialize_nat();
    initialize_int();
    initialize_char();
    initialize_bool();

    sstream out;

    out << LEAN_VERSION_STRING;
    g_short_version_string = new std::string(out.str());
    if (std::strlen(LEAN_PLATFORM_TARGET) > 0) {
        out << ", " << LEAN_PLATFORM_TARGET;
    }
    if (std::strlen(LEAN_GITHASH) > 0) {
        out << ", commit " << std::string(LEAN_GITHASH).substr(0, 12);
    }
    g_version_string = new std::string(out.str());

    g_util_fresh = new name("_util_fresh");
    mark_persistent(g_util_fresh->raw());
    register_name_generator_prefix(*g_util_fresh);
}

void finalize_library_util() {
    delete g_util_fresh;
    delete g_version_string;
    finalize_bool();
    finalize_int();
    finalize_nat();
    finalize_char();
    delete g_true;
    delete g_true_intro;
    delete g_and;
    delete g_and_intro;
    delete g_and_left;
    delete g_and_right;
    delete g_unit_mk;
    delete g_unit;
}
}

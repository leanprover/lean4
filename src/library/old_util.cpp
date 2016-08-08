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
#include "library/old_util.h"
#include "library/constants.h"
#include "library/unfold_macros.h"
#include "library/pp_options.h"
#include "library/projection.h"
#include "library/old_type_checker.h"

namespace lean {
expr to_telescope(old_type_checker & tc, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo,
                  constraint_seq & cs) {
    expr new_type = tc.whnf(type, cs);
    while (is_pi(new_type)) {
        type = new_type;
        expr local;
        if (binfo)
            local = mk_local(mk_fresh_name(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(mk_fresh_name(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type     = instantiate(binding_body(type), local);
        new_type = tc.whnf(type, cs);
    }
    return type;
}

expr to_telescope(old_type_checker & tc, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    constraint_seq cs;
    return to_telescope(tc, type, telescope, binfo, cs);
}

expr mk_and_intro(old_type_checker & ctx, expr const & Ha, expr const & Hb) {
    return mk_and_intro(ctx.get_type_context(), Ha, Hb);
}

expr mk_and_elim_left(old_type_checker & ctx, expr const & H) {
    return mk_and_elim_left(ctx.get_type_context(), H);
}

expr mk_and_elim_right(old_type_checker & ctx, expr const & H) {
    return mk_and_elim_right(ctx.get_type_context(), H);
}

expr mk_prod(old_type_checker & ctx, expr const & A, expr const & B) {
    return mk_prod(ctx.get_type_context(), A, B);
}

expr mk_pair(old_type_checker & ctx, expr const & a, expr const & b) {
    return mk_pair(ctx.get_type_context(), a, b);
}

expr mk_pr1(old_type_checker & ctx, expr const & p) {
    return mk_pr1(ctx.get_type_context(), p);
}

expr mk_pr2(old_type_checker & ctx, expr const & p) {
    return mk_pr2(ctx.get_type_context(), p);
}

expr mk_prod(old_type_checker & ctx, expr const & a, expr const & b, bool prop) {
    return mk_prod(ctx.get_type_context(), a, b, prop);
}
expr mk_pair(old_type_checker & ctx, expr const & a, expr const & b, bool prop) {
    return mk_pair(ctx.get_type_context(), a, b, prop);
}
expr mk_pr1(old_type_checker & ctx, expr const & p, bool prop) {
    return mk_pr1(ctx.get_type_context(), p, prop);
}
expr mk_pr2(old_type_checker & ctx, expr const & p, bool prop) {
    return mk_pr2(ctx.get_type_context(), p, prop);
}

expr mk_eq(old_type_checker & ctx, expr const & lhs, expr const & rhs) {
    return mk_eq(ctx.get_type_context(), lhs, rhs);
}

expr mk_refl(old_type_checker & ctx, expr const & a) {
    return mk_eq_refl(ctx.get_type_context(), a);
}

expr mk_symm(old_type_checker & ctx, expr const & H) {
    return mk_eq_symm(ctx.get_type_context(), H);
}

expr mk_trans(old_type_checker & ctx, expr const & H1, expr const & H2) {
    return mk_eq_trans(ctx.get_type_context(), H1, H2);
}

expr mk_subst(old_type_checker & ctx, expr const & motive,
              expr const & x, expr const & y, expr const & xeqy, expr const & h) {
    return mk_eq_subst(ctx.get_type_context(), motive, x, y, xeqy, h);
}

expr mk_subst(old_type_checker & ctx, expr const & motive, expr const & xeqy, expr const & h) {
    return mk_eq_subst(ctx.get_type_context(), motive, xeqy, h);
}

expr mk_subsingleton_elim(old_type_checker & ctx, expr const & h, expr const & x, expr const & y) {
    return mk_subsingleton_elim(ctx.get_type_context(), h, x, y);
}

expr mk_heq(old_type_checker & ctx, expr const & lhs, expr const & rhs) {
    return mk_heq(ctx.get_type_context(), lhs, rhs);
}

bool is_eq_a_a(old_type_checker & tc, expr const & e) {
    return is_eq_a_a(tc.get_type_context(), e);
}

expr mk_false_rec(old_type_checker & ctx, expr const & f, expr const & t) {
    return mk_false_rec(ctx.get_type_context(), f, t);
}

expr mk_not(old_type_checker & tc, expr const & e) {
    return mk_not(tc.get_type_context(), e);
}

expr mk_absurd(old_type_checker & ctx, expr const & t, expr const & e, expr const & not_e) {
    return mk_absurd(ctx.get_type_context(), t, e, not_e);
}

optional<expr> lift_down_if_hott(old_type_checker & ctx, expr const & v) {
    return lift_down_if_hott(ctx.get_type_context(), v);
}

void mk_telescopic_eq(old_type_checker & tc, buffer<expr> const & t, buffer<expr> const & s, buffer<expr> & eqs) {
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
        expr eq = mk_local(mk_fresh_name(), e_name.append_after(i+1), mk_eq(tc, t_i, s_i), binder_info());
        eqs.push_back(eq);
    }
}

void mk_telescopic_eq(old_type_checker & tc, buffer<expr> const & t, buffer<expr> & eqs) {
    lean_assert(std::all_of(t.begin(), t.end(), is_local));
    lean_assert(inductive::has_dep_elim(tc.env(), get_eq_name()));
    buffer<expr> s;
    for (unsigned i = 0; i < t.size(); i++) {
        expr ty = mlocal_type(t[i]);
        ty = abstract_locals(ty, i, t.data());
        ty = instantiate_rev(ty, i, s.data());
        expr local = mk_local(mk_fresh_name(), local_pp_name(t[i]).append_after("'"), ty, local_info(t[i]));
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

expr telescope_to_sigma(old_type_checker & tc, unsigned sz, expr const * ts, constraint_seq & cs) {
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

expr mk_sigma_mk(old_type_checker & tc, unsigned sz, expr const * ts, expr const * as, constraint_seq & cs) {
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

expr mk_sigma_mk(old_type_checker & tc, buffer<expr> const & ts, buffer<expr> const & as, constraint_seq & cs) {
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

void check_term(old_type_checker & tc, expr const & e) {
    expr tmp = unfold_untrusted_macros(tc.env(), e);
    tc.check_ignore_undefined_universes(tmp);
}

void check_term(environment const & env, expr const & e) {
    expr tmp = unfold_untrusted_macros(env, e);
    old_type_checker(env).check_ignore_undefined_universes(tmp);
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
    bool compact     = get_pp_goal_compact(opts);
    unsigned max_hs  = get_pp_goal_max_hyps(opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    format r;
    unsigned i     = std::min(max_hs, hyps.size());
    bool first     = true;
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
    if (hyps.size() > max_hs)
        r = r + compose(comma(), line()) + format("... (set pp.goal.max_hypotheses to display remaining hypotheses)");
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
            expr new_type = old_type_checker(env).infer(new_m).first;
            buffer<expr> hyps;
            get_app_args(new_m, hyps);
            return format("failed to synthesize placeholder") + line() + format_goal(fmt, hyps, new_type, subst);
        });
}

old_type_checker_ptr mk_type_checker(environment const & env, name_predicate const & pred) {
    return std::unique_ptr<old_type_checker>(new old_type_checker(env,
                                                          std::unique_ptr<old_converter>(new hint_old_converter<projection_converter>(env, pred))));
}

old_type_checker_ptr mk_simple_type_checker(environment const & env, name_predicate const & pred) {
    return std::unique_ptr<old_type_checker>(new old_type_checker(env,
                                                          std::unique_ptr<old_converter>(new hint_old_converter<old_default_converter>(env, pred))));
}

bool is_internal_name(name const & n) {
    return !n.is_anonymous() && n.is_string() && n.get_string() && n.get_string()[0] == '_';
}
}

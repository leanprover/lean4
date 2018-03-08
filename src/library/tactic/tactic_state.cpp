/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/type_context.h"
#include "library/pp_options.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/cache_helper.h"
#include "library/module.h"
#include "library/check.h"
#include "library/documentation.h"
#include "library/scoped_ext.h"
#include "library/aux_definition.h"
#include "library/unfold_macros.h"
#include "library/inductive_compiler/ginductive.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_exceptional.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_io.h"
#include "library/vm/interaction_state_imp.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/simp_lemmas.h"

namespace lean {
/* is_ts_safe is required by the interaction_state implementation. */
bool is_ts_safe(tactic_state const & s) { return s.us().m_mem.empty(); }
template struct interaction_monad<tactic_state>;

void tactic_state_cell::dealloc() {
    delete this;
}

tactic_state::tactic_state(environment const & env, options const & o, name const & decl_name, metavar_context const & ctx,
                           list<expr> const & gs, expr const & main, defeq_canonizer::state const & dcs,
                           context_cache_id const & cid, tactic_user_state const & us, tag_info const & tinfo) {
    m_ptr = new tactic_state_cell(env, o, decl_name, ctx, gs, main, dcs, cid, us, tinfo);
    m_ptr->inc_ref();
}

optional<expr> tactic_state::get_main_goal() const {
    if (empty(goals())) return none_expr();
    return some_expr(head(goals()));
}

optional<metavar_decl> tactic_state::get_main_goal_decl() const {
    if (empty(goals())) return optional<metavar_decl>();
    return mctx().find_metavar_decl(head(goals()));
}

tactic_state mk_tactic_state_for(environment const & env, options const & o, name const & decl_name,
                                 metavar_context mctx, local_context const & lctx, expr const & type) {
    expr main = mctx.mk_metavar_decl(lctx, type);
    return tactic_state(env, o, decl_name, mctx, list<expr>(main), main, defeq_canonizer::state(), unique_id(), tactic_user_state(), tag_info());
}

tactic_state mk_tactic_state_for(environment const & env, options const & o, name const & decl_name,
                                 local_context const & lctx, expr const & type) {
    return mk_tactic_state_for(env, o, decl_name, metavar_context(), lctx, type);
}

tactic_state mk_tactic_state_for_metavar(environment const & env, options const & opts, name const & decl_name,
                                         metavar_context const & mctx, expr const & mvar) {
    return tactic_state(env, opts, decl_name, mctx, list<expr>(mvar), mvar, defeq_canonizer::state(), unique_id(), tactic_user_state(), tag_info());
}

tactic_state set_options(tactic_state const & s, options const & o) {
    return tactic_state(s.env(), o, s.decl_name(), s.mctx(), s.goals(), s.main(), s.dcs(), s.cid(), s.us(), s.tinfo());
}

tactic_state set_env(tactic_state const & s, environment const & env) {
    return tactic_state(env, s.get_options(), s.decl_name(), s.mctx(), s.goals(), s.main(), s.dcs(), s.cid(), s.us(), s.tinfo());
}

tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx) {
    if (is_eqp(s.mctx(), mctx)) return s;
    return tactic_state(s.env(), s.get_options(), s.decl_name(), mctx, s.goals(), s.main(), s.dcs(), s.cid(), s.us(), s.tinfo());
}

tactic_state set_mctx_dcs(tactic_state const & s, metavar_context const & mctx, defeq_can_state const & dcs) {
    if (is_eqp(s.mctx(), mctx) && is_eqp(s.dcs(), dcs)) return s;
    return tactic_state(s.env(), s.get_options(), s.decl_name(), mctx, s.goals(), s.main(), dcs, s.cid(), s.us(), s.tinfo());
}

tactic_state set_env_mctx(tactic_state const & s, environment const & env, metavar_context const & mctx) {
    return tactic_state(env, s.get_options(), s.decl_name(), mctx, s.goals(), s.main(), s.dcs(), s.cid(), s.us(), s.tinfo());
}

static list<expr> consume_solved_prefix(metavar_context const & mctx, list<expr> const & gs) {
    if (empty(gs))
        return gs;
    else if (mctx.is_assigned(head(gs)))
        return consume_solved_prefix(mctx, tail(gs));
    else
        return gs;
}

tactic_state set_goals(tactic_state const & s, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), s.decl_name(), s.mctx(), consume_solved_prefix(s.mctx(), gs),
                        s.main(), s.dcs(), s.cid(), s.us(), s.tinfo());
}

tactic_state set_mctx_goals_dcs(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs, defeq_can_state const & dcs) {
    return tactic_state(s.env(), s.get_options(), s.decl_name(), mctx, consume_solved_prefix(mctx, gs), s.main(), dcs,
                        s.cid(), s.us(), s.tinfo());
}

tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs) {
    return set_mctx_goals_dcs(s, mctx, gs, s.dcs());
}

tactic_state set_env_mctx_goals(tactic_state const & s, environment const & env,
                                metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(env, s.get_options(), s.decl_name(), mctx, consume_solved_prefix(mctx, gs),
                        s.main(), s.dcs(), s.cid(), s.us(), s.tinfo());
}

tactic_state set_mctx_lctx_dcs(tactic_state const & s, metavar_context const & mctx, local_context const & lctx, defeq_can_state const & dcs) {
    if (is_eqp(s.mctx(), mctx) && is_eqp(s.dcs(), dcs)) {
        optional<metavar_decl> mdecl = s.get_main_goal_decl();
        if (mdecl && is_decl_eqp(mdecl->get_context(), lctx))
            return s;
    }
    metavar_context new_mctx = mctx;
    expr mvar = new_mctx.mk_metavar_decl(lctx, mk_true());
    return tactic_state(s.env(), s.get_options(), s.decl_name(), new_mctx, to_list(mvar), mvar, s.dcs(),
                        s.cid(), s.us(), s.tinfo());
}

tactic_state set_mctx_lctx(tactic_state const & s, metavar_context const & mctx, local_context const & lctx) {
    return set_mctx_lctx_dcs(s, mctx, lctx, s.dcs());
}

tactic_state set_defeq_can_state(tactic_state const & s, defeq_can_state const & dcs) {
    if (is_eqp(s.dcs(), dcs)) return s;
    return tactic_state(s.env(), s.get_options(), s.decl_name(), s.mctx(), s.goals(), s.main(), dcs,
                        s.cid(), s.us(), s.tinfo());
}

tactic_state set_user_state(tactic_state const & s, tactic_user_state const & us) {
    return tactic_state(s.env(), s.get_options(), s.decl_name(), s.mctx(), s.goals(), s.main(), s.dcs(),
                        s.cid(), us, s.tinfo());
}

tactic_state set_tag_info(tactic_state const & s, tag_info const & tinfo) {
    return tactic_state(s.env(), s.get_options(), s.decl_name(), s.mctx(), s.goals(), s.main(), s.dcs(),
                        s.cid(), s.us(), tinfo);
}

tactic_state set_context_cache_id(tactic_state const & s, context_cache_id const & cid) {
    return tactic_state(s.env(), s.get_options(), s.decl_name(), s.mctx(), s.goals(), s.main(), s.dcs(),
                        cid, s.us(), s.tinfo());
}

format tactic_state::pp_expr(formatter_factory const & fmtf, expr const & e) const {
    type_context_old ctx = mk_cacheless_type_context_for(*this, transparency_mode::All);
    formatter fmt = fmtf(env(), get_options(), ctx);
    return fmt(e);
}

static format pp_tag(list<name> const & tag) {
    buffer<name> tmp;
    for (auto n : tag) {
        if (!is_internal_name(n))
            tmp.push_back(n);
    }
    unsigned i = tmp.size();
    if (i == 0) return format();
    format r;
    while (i > 0) {
        --i;
        r += format(tmp[i]);
        if (i > 0)
            r += comma() + space();
    }
    return format("case") + space() + r + line();
}

format tactic_state::pp_goal(formatter_factory const & fmtf, expr const & g, bool target_lhs_only) const {
    options opts               = get_options().update_if_undef(get_pp_purify_locals_name(), false);
    bool inst_mvars            = get_pp_instantiate_mvars(opts);
    metavar_decl decl          = mctx().get_metavar_decl(g);
    local_context lctx         = decl.get_context();
    metavar_context mctx_tmp   = mctx();
    type_context_old ctx(env(), get_options(), mctx_tmp, lctx, transparency_mode::All);
    formatter fmt              = fmtf(env(), opts, ctx);
    if (inst_mvars)
        lctx                   = lctx.instantiate_mvars(mctx_tmp);
    format r;
    if (auto tag = get_tag_info().m_tags.find(g)) {
        r                    += pp_tag(*tag);
    }
    r                         += lctx.pp(fmt);
    unsigned indent            = get_pp_indent(get_options());
    bool unicode               = get_pp_unicode(get_options());
    if (!lctx.empty())
        r += line();
    expr type                  = decl.get_type();
    if (inst_mvars)
        type                   = mctx_tmp.instantiate_mvars(type);
    expr rel, lhs, rhs;
    if (target_lhs_only && is_simp_relation(env(), type, rel, lhs, rhs)) {
        r += format("|") + space() + nest(indent, fmt(lhs));
    } else {
        format turnstile(unicode ? "⊢" : "|-");
        r += turnstile + space() + nest(indent, fmt(type));
    }
    if (get_pp_goal_compact(get_options()))
        r = group(r);
    return r;
}

format tactic_state::pp_core(formatter_factory const & fmtf, bool target_lhs_only) const {
    format r;
    bool first = true;
    unsigned num_goals = length(goals());
    if (length(goals()) > 1)
        r += format(num_goals) + space() + format("goals") + line();
    for (auto const & g : goals()) {
        if (first) first = false; else r += line() + line();
        r += pp_goal(fmtf, g, target_lhs_only);
    }
    if (first) r = format("no goals");
    return r;
}

format tactic_state::pp_core(bool target_lhs_only) const {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return pp_core(fmtf, target_lhs_only);
}

format tactic_state::pp_expr(expr const & e) const {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return pp_expr(fmtf, e);
}

format tactic_state::pp_goal(expr const & g) const {
    lean_assert(is_metavar(g));
    lean_assert(mctx().find_metavar_decl(g));
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return pp_goal(fmtf, g);
}

vm_obj to_obj(tactic_state const & s) {
    return tactic::to_obj(s);
}

transparency_mode to_transparency_mode(vm_obj const & o) {
    return static_cast<transparency_mode>(cidx(o));
}

vm_obj to_obj(transparency_mode m) {
    return mk_vm_simple(static_cast<unsigned>(m));
}

vm_obj tactic_state_env(vm_obj const & s) {
    return to_obj(tactic::to_state(s).env());
}

vm_obj tactic_state_to_format(vm_obj const & s, vm_obj const & target_lhs_only) {
    return to_obj(tactic::to_state(s).pp_core(to_bool(target_lhs_only)));
}

format pp_expr(tactic_state const & s, expr const & e) {
    expr new_e      = e;
    bool inst_mvars = get_pp_instantiate_mvars(s.get_options());
    if (inst_mvars)
        new_e       = metavar_context(s.mctx()).instantiate_mvars(e);
    return s.pp_expr(new_e);
}

format pp_indented_expr(tactic_state const & s, expr const & e) {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return nest(get_pp_indent(s.get_options()), line() + s.pp_expr(fmtf, e));
}

vm_obj tactic_state_format_expr(vm_obj const & s, vm_obj const & e) {
    return to_obj(pp_expr(tactic::to_state(s), to_expr(e)));
}

vm_obj mk_no_goals_exception(tactic_state const & s) {
    return tactic::mk_exception("tactic failed, there are no goals to be solved", s);
}

vm_obj tactic_result(vm_obj const & o) {
    tactic_state const & s = tactic::to_state(o);
    metavar_context mctx = s.mctx();
    expr r = mctx.instantiate_mvars(s.main());
    return tactic::mk_success(to_obj(r), set_mctx(s, mctx));
}

vm_obj tactic_format_result(vm_obj const & o) {
    tactic_state const & s = tactic::to_state(o);
    metavar_context mctx = s.mctx();
    expr r = mctx.instantiate_mvars(s.main());
    metavar_decl main_decl = mctx.get_metavar_decl(s.main());
    type_context_old ctx(s.env(), s.get_options(), mctx, main_decl.get_context(), transparency_mode::All);
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    formatter fmt = fmtf(s.env(), s.get_options(), ctx);
    return tactic::mk_success(to_obj(fmt(r)), s);
}

vm_obj tactic_target(vm_obj const & o) {
    tactic_state const & s = tactic::to_state(o);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    return tactic::mk_success(to_obj(g->get_type()), s);
}

tactic_state_context_cache::tactic_state_context_cache(tactic_state & s):
    persistent_context_cache(s.get_cache_id(), s.get_options()),
    m_state(set_context_cache_id(s, get_id())) {
    s       = m_state;
}

type_context_old tactic_state_context_cache::mk_type_context(tactic_state const & s, local_context const & lctx, transparency_mode m) {
    lean_assert(s.get_cache_id() == m_state.get_cache_id());
    return type_context_old(s.env(), s.mctx(), lctx, *this, m);
}

type_context_old tactic_state_context_cache::mk_type_context(tactic_state const & s, transparency_mode m) {
    local_context lctx;
    if (auto d = s.get_main_goal_decl()) lctx = d->get_context();
    return mk_type_context(s, lctx, m);
}

type_context_old tactic_state_context_cache::mk_type_context(transparency_mode m) {
    return mk_type_context(m_state, m);
}

type_context_old mk_type_context_for(environment const & env, options const & o, metavar_context const & mctx,
                                 local_context const & lctx, transparency_mode m) {
    return type_context_old(env, o, mctx, lctx, m);
}

type_context_old mk_type_context_for(tactic_state const & s, local_context const & lctx, transparency_mode m) {
    return mk_type_context_for(s.env(), s.get_options(), s.mctx(), lctx, m);
}

type_context_old mk_type_context_for(tactic_state const & s, transparency_mode m) {
    local_context lctx;
    if (auto d = s.get_main_goal_decl()) lctx = d->get_context();
    return mk_type_context_for(s, lctx, m);
}

type_context_old mk_type_context_for(vm_obj const & s) {
    return mk_type_context_for(tactic::to_state(s));
}

type_context_old mk_type_context_for(vm_obj const & s, vm_obj const & m) {
    return mk_type_context_for(tactic::to_state(s), to_transparency_mode(m));
}

type_context_old mk_cacheless_type_context_for(tactic_state const & s, transparency_mode m) {
    return mk_type_context_for(s, m);
}

static void check_closed(char const * tac_name, expr const & e) {
    if (!closed(e))
        throw exception(sstream() << "tactic '" << tac_name << "' failed, "
                        "given expression should not contain de-Bruijn variables, "
                        "they should be replaced with local constants before using this tactic");
}

vm_obj tactic_infer_type(vm_obj const & e, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context();
    try {
        check_closed("infer_type", to_expr(e));
        return tactic::mk_success(to_obj(ctx.infer(to_expr(e))), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_whnf(vm_obj const & e, vm_obj const & t, vm_obj const & unfold_ginductive, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context(to_transparency_mode(t));
    try {
        check_closed("whnf", to_expr(e));
        if (to_bool(unfold_ginductive)) {
            return tactic::mk_success(to_obj(ctx.whnf(to_expr(e))), s);
        } else {
            return tactic::mk_success(to_obj(whnf_ginductive_gintro_rule(ctx, to_expr(e))), s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_head_eta_expand(vm_obj const & e, vm_obj const & s0) {
    tactic_state s   = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context();
    try {
        check_closed("head_eta_expand", to_expr(e));
        return tactic::mk_success(to_obj(ctx.eta_expand(to_expr(e))), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_head_eta(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s = tactic::to_state(s0);
    try {
        return tactic::mk_success(to_obj(try_eta(to_expr(e))), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_head_beta(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s = tactic::to_state(s0);
    try {
        return tactic::mk_success(to_obj(annotated_head_beta_reduce(to_expr(e))), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_head_zeta(vm_obj const & e0, vm_obj const & s0) {
    tactic_state const & s = tactic::to_state(s0);
    try {
        expr const & e = to_expr(e0);
        check_closed("head_zeta", e);
        if (!is_local(e)) return tactic::mk_success(e0, s);
        optional<metavar_decl> mdecl = s.get_main_goal_decl();
        if (!mdecl) return tactic::mk_success(e0, s);
        local_context lctx = mdecl->get_context();
        optional<local_decl> ldecl = lctx.find_local_decl(e);
        if (!ldecl || !ldecl->get_value()) return tactic::mk_success(e0, s);
        return tactic::mk_success(to_obj(*ldecl->get_value()), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_zeta(vm_obj const & e0, vm_obj const & s0) {
    tactic_state const & s = tactic::to_state(s0);
    try {
        expr const & e = to_expr(e0);
        check_closed("zeta", e);
        optional<metavar_decl> mdecl = s.get_main_goal_decl();
        if (!mdecl) return tactic::mk_success(e0, s);
        local_context lctx = mdecl->get_context();
        return tactic::mk_success(to_obj(zeta_expand(lctx, e)), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_is_class(vm_obj const & e, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context();
    try {
        check_closed("is_class", to_expr(e));
        return tactic::mk_success(mk_vm_bool(static_cast<bool>(ctx.is_class(to_expr(e)))), s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_mk_instance(vm_obj const & e, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context();
    try {
        check_closed("mk_instance", to_expr(e));
        if (auto r = ctx.mk_class_instance(to_expr(e))) {
            tactic_state new_s = set_mctx(s, ctx.mctx());
            return tactic::mk_success(to_obj(*r), new_s);
        } else {
            auto thunk = [=]() {
                format m("tactic.mk_instance failed to generate instance for");
                m += pp_indented_expr(s, to_expr(e));
                return m;
            };
            return tactic::mk_exception(thunk, s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

static vm_obj mk_unify_exception(char const * header, expr const & e1, expr const & e2, tactic_state const & s) {
    auto thunk = [=]() {
        format r(header);
        unsigned indent = get_pp_indent(s.get_options());
        formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
        type_context_old ctx   = mk_cacheless_type_context_for(s, transparency_mode::All);
        formatter fmt      = fmtf(s.env(), s.get_options(), ctx);
        expr e1_type       = ctx.infer(e1);
        expr e2_type       = ctx.infer(e2);
        format e1_fmt      = fmt(e1);
        format e1_type_fmt = fmt(e1_type);
        format e2_fmt      = fmt(e2);
        format e2_type_fmt = fmt(e2_type);
        r += nest(indent, line() + group(e1_fmt + line() + format(": ") + e1_type_fmt));
        r += line() + format("and");
        r += nest(indent, line() + group(e2_fmt + line() + format(": ") + e2_type_fmt));
        return r;
    };
    return tactic::mk_exception(thunk, s);
}

vm_obj tactic_unify(vm_obj const & e1, vm_obj const & e2, vm_obj const & t, vm_obj const & approx, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx       = cache.mk_type_context(to_transparency_mode(t));
    try {
        check_closed("unify", to_expr(e1));
        check_closed("unify", to_expr(e2));
        type_context_old::approximate_scope scope(ctx, to_bool(approx));
        bool r = ctx.is_def_eq(to_expr(e1), to_expr(e2));
        if (r) {
            return tactic::mk_success(set_mctx(s, ctx.mctx()));
        } else {
            return mk_unify_exception("unify tactic failed, failed to unify",
                                      to_expr(e1), to_expr(e2), s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_is_def_eq(vm_obj const & e1, vm_obj const & e2, vm_obj const & t, vm_obj const & approx, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context(to_transparency_mode(t));
    try {
        check_closed("is_def_eq", to_expr(e1));
        check_closed("is_def_eq", to_expr(e2));
        type_context_old::approximate_scope scope(ctx, to_bool(approx));
        bool r = ctx.pure_is_def_eq(to_expr(e1), to_expr(e2));
        if (r) {
            return tactic::mk_success(s);
        } else {
            return mk_unify_exception("is_def_eq tactic failed, the following expressions are not definitionally equal "
                                      "(remark: is_def_eq tactic does modify the metavariable assignment)",
                                      to_expr(e1), to_expr(e2), s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_get_local(vm_obj const & n, vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx       = g->get_context();
    optional<local_decl> d   = lctx.find_local_decl_from_user_name(to_name(n));
    if (!d) return tactic::mk_exception(sstream() << "get_local tactic failed, unknown '" << to_name(n) << "' local", s);
    return tactic::mk_success(to_obj(d->mk_ref()), s);
}

vm_obj tactic_local_context(vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx       = g->get_context();
    buffer<expr> r;
    lctx.for_each([&](local_decl const & d) { r.push_back(d.mk_ref()); });
    return tactic::mk_success(to_obj(to_list(r)), s);
}

vm_obj tactic_get_unused_name(vm_obj const & n, vm_obj const & vm_i, vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    name unused_name;
    if (is_none(vm_i)) {
        unused_name = g->get_context().get_unused_name(to_name(n));
    } else {
        unsigned i  = force_to_unsigned(get_some_value(vm_i), 0);
        unused_name = g->get_context().get_unused_name(to_name(n), i);
    }
    return tactic::mk_success(to_obj(unused_name), s);
}

vm_obj rotate_left(unsigned n, tactic_state const & s) {
    buffer<expr> gs;
    to_buffer(s.goals(), gs);
    unsigned sz = gs.size();
    if (sz == 0)
        return tactic::mk_success(s);
    n = n%sz;
    std::rotate(gs.begin(), gs.begin() + n, gs.end());
    return tactic::mk_success(set_goals(s, to_list(gs)));
}

vm_obj tactic_rotate_left(vm_obj const & n, vm_obj const & s) {
    return rotate_left(force_to_unsigned(n, 0), tactic::to_state(s));
}

vm_obj tactic_get_goals(vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    return tactic::mk_success(to_obj(s.goals()), s);
}

vm_obj set_goals(list<expr> const & gs, tactic_state const & s) {
    buffer<expr> new_gs;
    metavar_context const & mctx = s.mctx();
    for (expr const & g : gs) {
        if (!mctx.find_metavar_decl(g)) {
            return tactic::mk_exception("invalid set_goals tactic, expressions must be meta-variables "
                                       "that have been declared in the current tactic_state", s);
        }
        if (!mctx.is_assigned(g))
            new_gs.push_back(g);
    }
    return tactic::mk_success(set_goals(s, to_list(new_gs)));
}

vm_obj tactic_set_goals(vm_obj const & gs, vm_obj const & s) {
    return set_goals(to_list_expr(gs), tactic::to_state(s));
}

vm_obj tactic_mk_meta_univ(vm_obj const & s) {
    metavar_context mctx = tactic::to_state(s).mctx();
    level u = mctx.mk_univ_metavar_decl();
    return tactic::mk_success(to_obj(u), set_mctx(tactic::to_state(s), mctx));
}

vm_obj tactic_mk_meta_var(vm_obj const & t, vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    metavar_context mctx     = s.mctx();
    local_context lctx;
    if (optional<metavar_decl> g = s.get_main_goal_decl()) {
        lctx = g->get_context();
    }
    expr m = mctx.mk_metavar_decl(lctx, to_expr(t));
    return tactic::mk_success(to_obj(m), set_mctx(s, mctx));
}

vm_obj tactic_get_univ_assignment(vm_obj const & u, vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    metavar_context mctx     = s.mctx();
    if (!is_meta(to_level(u))) {
        return tactic::mk_exception("get_univ_assignment tactic failed, argument is not an universe metavariable", s);
    } else if (auto r = mctx.get_assignment(to_level(u))) {
        return tactic::mk_success(to_obj(*r), s);
    } else {
        return tactic::mk_exception("get_univ_assignment tactic failed, universe metavariable is not assigned", s);
    }
}

vm_obj tactic_get_assignment(vm_obj const & e, vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    metavar_context mctx     = s.mctx();
    if (!is_metavar(to_expr(e))) {
        return tactic::mk_exception("get_assignment tactic failed, argument is not a metavariable", s);
    } else if (auto r = mctx.get_assignment(to_expr(e))) {
        return tactic::mk_success(to_obj(*r), s);
    } else {
        return tactic::mk_exception("get_assignment tactic failed, metavariable is not assigned", s);
    }
}

vm_obj tactic_is_assigned(vm_obj const & g, vm_obj const & s0) {
    tactic_state const & s   = tactic::to_state(s0);
    if (!is_metavar(to_expr(g))) {
        return tactic::mk_exception("is_assigned tactic failed, argument is not a metavariable", s);
    } else {
        return tactic::mk_success(mk_vm_bool(s.mctx().is_assigned(to_expr(g))), s);
    }
}

vm_obj tactic_state_get_options(vm_obj const & s) {
    return to_obj(tactic::to_state(s).get_options());
}

vm_obj tactic_state_set_options(vm_obj const & s, vm_obj const & o) {
    return to_obj(set_options(tactic::to_state(s), to_options(o)));
}

vm_obj tactic_mk_fresh_name(vm_obj const & s) {
    return tactic::mk_success(to_obj(mk_fresh_name()), tactic::to_state(s));
}

vm_obj tactic_is_trace_enabled_for(vm_obj const & n) {
    return mk_vm_bool(is_trace_class_enabled(to_name(n)));
}

vm_obj tactic_instantiate_mvars(vm_obj const & e, vm_obj const & _s) {
    tactic_state const & s = tactic::to_state(_s);
    metavar_context mctx = s.mctx();
    expr r = mctx.instantiate_mvars(to_expr(e));
    return tactic::mk_success(to_obj(r), set_mctx(s, mctx));
}

vm_obj tactic_add_decl(vm_obj const & _d, vm_obj const & _s) {
    tactic_state const & s  = tactic::to_state(_s);
    try {
        declaration d       = to_declaration(_d);
        environment new_env = module::add(s.env(), check(s.env(), d));
        new_env = vm_compile(new_env, d);
         return tactic::mk_success(set_env(s, new_env));
    } catch (throwable & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_set_env(vm_obj const & _env, vm_obj const & _s) {
    tactic_state const & s      = tactic::to_state(_s);
    environment const & new_env = to_env(_env);
    if (new_env.is_descendant(s.env()))
        return tactic::mk_success(set_env(s, new_env));
    else
        return tactic::mk_exception(sstream() << "new environment is not a descendent from old environment.", s);
}

vm_obj tactic_open_namespaces(vm_obj const & s) {
    environment env = tactic::to_state(s).env();
    buffer<name> b;
    to_buffer(get_namespaces(env), b);
    get_opened_namespaces(env).to_buffer(b);
    return tactic::mk_success(to_obj(b), tactic::to_state(s));
}

vm_obj tactic_doc_string(vm_obj const & n, vm_obj const & _s) {
    tactic_state const & s  = tactic::to_state(_s);
    if (optional<std::string> doc = get_doc_string(s.env(), to_name(n))) {
        return tactic::mk_success(to_obj(*doc), s);
    } else {
        return tactic::mk_exception(sstream() << "no doc string for '" << to_name(n) << "'", s);
    }
}

vm_obj tactic_add_doc_string(vm_obj const & n, vm_obj const & doc, vm_obj const & _s) {
    tactic_state const & s  = tactic::to_state(_s);
    try {
        environment new_env = add_doc_string(s.env(), to_name(n), to_string(doc));
        return tactic::mk_success(set_env(s, new_env));
    } catch (throwable & ex) {
        return tactic::mk_exception(ex, s);
    }
}

/* meta constant module_doc_strings : tactic (list (option name × string)) */
vm_obj tactic_module_doc_strings(vm_obj const & _s) {
    tactic_state const & s  = tactic::to_state(_s);
    buffer<doc_entry> entries;
    get_module_doc_strings(s.env(), entries);
    unsigned i = entries.size();
    vm_obj r   = mk_vm_simple(0);
    while (i > 0) {
        --i;
        vm_obj decl_name;
        if (auto d = entries[i].get_decl_name())
            decl_name = mk_vm_some(to_obj(*d));
        else
            decl_name = mk_vm_none();
        vm_obj doc = to_obj(entries[i].get_doc());
        vm_obj e   = mk_vm_pair(decl_name, doc);
        r          = mk_vm_constructor(1, e, r);
    }
    return tactic::mk_success(r, s);
}

vm_obj tactic_decl_name(vm_obj const & _s) {
    auto & s = tactic::to_state(_s);
    return tactic::mk_success(to_obj(s.decl_name()), s);
}

format tactic_state::pp() const {
    type_context_old ctx = mk_cacheless_type_context_for(*this, transparency_mode::Semireducible);
    expr ts_expr     = mk_constant("tactic_state");
    optional<expr> to_fmt_inst = ctx.mk_class_instance(mk_app(mk_constant("has_to_format", {mk_level_zero()}), ts_expr));
    if (!to_fmt_inst) {
        return pp_core();
    } else {
        try {
            expr code            = mk_app(mk_constant("to_fmt", {mk_level_zero()}), ts_expr, *to_fmt_inst);
            expr type            = ctx.infer(code);
            environment new_env  = ctx.env();
            bool use_conv_opt    = true;
            bool is_trusted      = false;
            name pp_name("_pp_tactic_state");
            auto cd              = check(new_env, mk_definition(new_env, pp_name, {}, type, code, use_conv_opt, is_trusted));
            new_env              = new_env.add(cd);
            new_env              = vm_compile(new_env, new_env.get(pp_name));
            vm_state S(new_env, get_options());
            vm_obj r             = S.invoke(pp_name, to_obj(*this));
            std::ostringstream ss;
            return to_format(r);
        } catch (exception &) {
            return pp_core();
        }
    }
}

vm_obj tactic_add_aux_decl(vm_obj const & n, vm_obj const & type, vm_obj const & val, vm_obj const & lemma, vm_obj const & _s) {
    tactic_state const & s   = tactic::to_state(_s);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    try {
        pair<environment, expr> r =
            to_bool(lemma) ?
              mk_aux_lemma(s.env(), s.mctx(), g->get_context(), to_name(n), to_expr(type), to_expr(val))
            : mk_aux_definition(s.env(), s.mctx(), g->get_context(), to_name(n), to_expr(type), to_expr(val));
        return tactic::mk_success(to_obj(r.second), set_env(s, r.first));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_unsafe_run_io(vm_obj const &, vm_obj const & a, vm_obj const & s) {
    vm_obj r = invoke(a, mk_vm_unit());
    if (optional<vm_obj> a = is_io_result(r)) {
        return tactic::mk_success(*a, tactic::to_state(s));
    } else {
        optional<vm_obj> e = is_io_error(r);
        lean_assert(e);
        return tactic::mk_exception(io_error_to_string(*e), tactic::to_state(s));
    }
}

vm_obj io_run_tactic(vm_obj const &, vm_obj const & tac, vm_obj const &) {
    vm_state & vm  = get_vm_state();
    tactic_state s = mk_tactic_state_for(vm.env(), vm.get_options(), "_io_run_tactic",
                                         metavar_context(), local_context(), mk_true());
    vm_obj r = invoke(tac, to_obj(s));
    if (tactic::is_result_success(r)) {
        return mk_io_result(tactic::get_success_value(r));
    } else {
        return mk_io_failure("tactic failed"); // TODO(Leo): improve exception message
    }
}

unsigned tactic_user_state::alloc(vm_obj const & v) {
    unsigned r;
    if (m_free_refs) {
        r  = head(m_free_refs);
        m_free_refs = tail(m_free_refs);
    } else {
        r = m_next_idx;
        m_next_idx++;
    }
    m_mem.insert(r, v);
    return r;
}

void tactic_user_state::dealloc(unsigned ref) {
    if (!m_mem.contains(ref)) {
        throw exception("invalid ref dealloc, invalid reference");
    }
    m_free_refs = cons(ref, m_free_refs);
    m_mem.erase(ref);
}

vm_obj tactic_user_state::read(unsigned ref) const {
    if (auto v = m_mem.find(ref)) {
        return *v;
    } else {
        throw exception("invalid read_ref, invalid reference");
    }
}

void tactic_user_state::write(unsigned ref, vm_obj const & o) {
    if (m_mem.contains(ref)) {
        m_mem.insert(ref, o);
    } else {
        throw exception("invalid write_ref, invalid reference");
    }
}

/*
meta constant using_new_ref {α : Type u} {β : Type v} (a : α) (t : ref α → tactic β) : tactic β
*/
vm_obj tactic_using_new_ref(vm_obj const &, vm_obj const &, vm_obj const & a, vm_obj const & t, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    try {
        tactic_user_state us = s.us();
        unsigned ref = us.alloc(a);
        s = set_user_state(s, us);
        vm_obj r = invoke(t, mk_vm_simple(ref), to_obj(s));
        if (tactic::is_result_success(r)) {
            vm_obj b = tactic::get_success_value(r);
            s        = tactic::to_state(tactic::get_success_state(r));
            us       = s.us();
            us.dealloc(ref);
            s        = set_user_state(s, us);
            return tactic::mk_success(b, s);
        } else {
            return r;
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

/*
meta constant read_ref {α : Type u} : ref α → tactic α
*/
vm_obj tactic_read_ref(vm_obj const &, vm_obj const & ref, vm_obj const & s0) {
    tactic_state const & s = tactic::to_state(s0);
    try {
        tactic_user_state const & us = s.us();
        vm_obj r = us.read(cidx(ref));
        return tactic::mk_success(r, s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

/*
meta constant write_ref {α : Type u} : ref α → α → tactic unit
*/
vm_obj tactic_write_ref(vm_obj const &, vm_obj const & ref, vm_obj const & v, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    try {
        tactic_user_state us = s.us();
        us.write(cidx(ref), v);
        s = set_user_state(s, us);
        return tactic::mk_success(s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_sleep(vm_obj const & msecs, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    if (optional<unsigned> m = try_to_unsigned(msecs)) {
        chrono::milliseconds cm(*m);
        sleep_for(cm);
        return tactic::mk_success(s);
    } else {
        return tactic::mk_exception("sleep failed, argument is too big", s);
    }
}

vm_obj tactic_type_check(vm_obj const & e, vm_obj const & m, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    try {
        tactic_state_context_cache cache(s);
        type_context_old ctx = cache.mk_type_context(to_transparency_mode(m));
        check(ctx, to_expr(e));
        return tactic::mk_success(s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_enable_tags(vm_obj const & b, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tag_info tinfo = s.tinfo();
    tinfo.m_tags_enabled = to_bool(b);
    return tactic::mk_success(set_tag_info(s, tinfo));
}

vm_obj tactic_tags_enabled(vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    return tactic::mk_success(mk_vm_bool(s.tinfo().m_tags_enabled), s);
}

vm_obj tactic_set_tag(vm_obj const & g, vm_obj const & t, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tag_info tinfo = s.tinfo();
    if (!tinfo.m_tags_enabled)
        return tactic::mk_success(s);
    if (is_nil(t)) {
        tinfo.m_tags.erase(to_expr(g));
    } else {
        tinfo.m_tags.insert(to_expr(g), to_list_name(t));
    }
    return tactic::mk_success(set_tag_info(s, tinfo));
}

vm_obj tactic_get_tag(vm_obj const & g, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tag_info const & tinfo = s.tinfo();
    if (auto t = tinfo.m_tags.find(to_expr(g))) {
        return tactic::mk_success(to_obj(*t), s);
    } else {
        return tactic::mk_success(mk_vm_nil(), s);
    }
}

vm_obj tactic_unfreeze_local_instances(vm_obj const & s0) {
    tactic_state s             = tactic::to_state(s0);
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx         = g->get_context();
    tactic_state_context_cache cache(s);
    type_context_old ctx           = cache.mk_type_context();
    lctx.unfreeze_local_instances();
    expr new_mvar              = ctx.mk_metavar_decl(lctx, g->get_type());
    ctx.assign(*s.get_main_goal(), new_mvar);
    tactic_state new_s = set_mctx_goals(s, ctx.mctx(), cons(new_mvar, tail(s.goals())));
    return tactic::mk_success(new_s);
}

vm_obj tactic_frozen_local_instances(vm_obj const & s0) {
    tactic_state s             = tactic::to_state(s0);
    optional<metavar_decl> g   = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    local_context lctx         = g->get_context();
    if (optional<local_instances> lis = lctx.get_frozen_local_instances()) {
        buffer<expr> li_buffer;
        for (local_instance const & li : *lis)
            li_buffer.push_back(li.get_local());
        return tactic::mk_success(mk_vm_some(to_obj(li_buffer)), s);
    } else {
        return tactic::mk_success(mk_vm_none(), s);
    }
}

void initialize_tactic_state() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "env"}),            tactic_state_env);
    DECLARE_VM_BUILTIN(name({"tactic_state", "format_expr"}),    tactic_state_format_expr);
    DECLARE_VM_BUILTIN(name({"tactic_state", "to_format"}),      tactic_state_to_format);
    DECLARE_VM_BUILTIN(name({"tactic_state", "get_options"}),    tactic_state_get_options);
    DECLARE_VM_BUILTIN(name({"tactic_state", "set_options"}),    tactic_state_set_options);
    DECLARE_VM_BUILTIN(name({"tactic", "target"}),               tactic_target);
    DECLARE_VM_BUILTIN(name({"tactic", "result"}),               tactic_result);
    DECLARE_VM_BUILTIN(name({"tactic", "is_assigned"}),          tactic_is_assigned);
    DECLARE_VM_BUILTIN(name({"tactic", "format_result"}),        tactic_format_result);
    DECLARE_VM_BUILTIN(name({"tactic", "infer_type"}),           tactic_infer_type);
    DECLARE_VM_BUILTIN(name({"tactic", "whnf"}),                 tactic_whnf);
    DECLARE_VM_BUILTIN(name({"tactic", "is_def_eq"}),            tactic_is_def_eq);
    DECLARE_VM_BUILTIN(name({"tactic", "head_eta_expand"}),      tactic_head_eta_expand);
    DECLARE_VM_BUILTIN(name({"tactic", "head_eta"}),             tactic_head_eta);
    DECLARE_VM_BUILTIN(name({"tactic", "head_beta"}),            tactic_head_beta);
    DECLARE_VM_BUILTIN(name({"tactic", "head_zeta"}),            tactic_head_zeta);
    DECLARE_VM_BUILTIN(name({"tactic", "zeta"}),                 tactic_zeta);
    DECLARE_VM_BUILTIN(name({"tactic", "is_class"}),             tactic_is_class);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_instance"}),          tactic_mk_instance);
    DECLARE_VM_BUILTIN(name({"tactic", "unify"}),                tactic_unify);
    DECLARE_VM_BUILTIN(name({"tactic", "get_local"}),            tactic_get_local);
    DECLARE_VM_BUILTIN(name({"tactic", "local_context"}),        tactic_local_context);
    DECLARE_VM_BUILTIN(name({"tactic", "get_unused_name"}),      tactic_get_unused_name);
    DECLARE_VM_BUILTIN(name({"tactic", "rotate_left"}),          tactic_rotate_left);
    DECLARE_VM_BUILTIN(name({"tactic", "get_goals"}),            tactic_get_goals);
    DECLARE_VM_BUILTIN(name({"tactic", "set_goals"}),            tactic_set_goals);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_meta_univ"}),         tactic_mk_meta_univ);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_meta_var"}),          tactic_mk_meta_var);
    DECLARE_VM_BUILTIN(name({"tactic", "get_univ_assignment"}),  tactic_get_univ_assignment);
    DECLARE_VM_BUILTIN(name({"tactic", "get_assignment"}),       tactic_get_assignment);
    DECLARE_VM_BUILTIN(name({"tactic", "mk_fresh_name"}),        tactic_mk_fresh_name);
    DECLARE_VM_BUILTIN(name({"tactic", "is_trace_enabled_for"}), tactic_is_trace_enabled_for);
    DECLARE_VM_BUILTIN(name({"tactic", "instantiate_mvars"}),    tactic_instantiate_mvars);
    DECLARE_VM_BUILTIN(name({"tactic", "add_decl"}),             tactic_add_decl);
    DECLARE_VM_BUILTIN(name({"tactic", "set_env"}),              tactic_set_env);
    DECLARE_VM_BUILTIN(name({"tactic", "doc_string"}),           tactic_doc_string);
    DECLARE_VM_BUILTIN(name({"tactic", "add_doc_string"}),       tactic_add_doc_string);
    DECLARE_VM_BUILTIN(name({"tactic", "module_doc_strings"}),   tactic_module_doc_strings);
    DECLARE_VM_BUILTIN(name({"tactic", "open_namespaces"}),      tactic_open_namespaces);
    DECLARE_VM_BUILTIN(name({"tactic", "decl_name"}),            tactic_decl_name);
    DECLARE_VM_BUILTIN(name({"tactic", "add_aux_decl"}),         tactic_add_aux_decl);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe_run_io"}),        tactic_unsafe_run_io);
    DECLARE_VM_BUILTIN(name({"tactic", "using_new_ref"}),        tactic_using_new_ref);
    DECLARE_VM_BUILTIN(name({"tactic", "read_ref"}),             tactic_read_ref);
    DECLARE_VM_BUILTIN(name({"tactic", "write_ref"}),            tactic_write_ref);
    DECLARE_VM_BUILTIN(name({"tactic", "sleep"}),                tactic_sleep);
    DECLARE_VM_BUILTIN(name({"tactic", "type_check"}),           tactic_type_check);
    DECLARE_VM_BUILTIN(name({"tactic", "enable_tags"}),          tactic_enable_tags);
    DECLARE_VM_BUILTIN(name({"tactic", "tags_enabled"}),         tactic_tags_enabled);
    DECLARE_VM_BUILTIN(name({"tactic", "set_tag"}),              tactic_set_tag);
    DECLARE_VM_BUILTIN(name({"tactic", "get_tag"}),              tactic_get_tag);
    DECLARE_VM_BUILTIN(name({"tactic", "unfreeze_local_instances"}), tactic_unfreeze_local_instances);
    DECLARE_VM_BUILTIN(name({"tactic", "frozen_local_instances"}),   tactic_frozen_local_instances);
    DECLARE_VM_BUILTIN(name({"io", "run_tactic"}),               io_run_tactic);
}

void finalize_tactic_state() {
}
}

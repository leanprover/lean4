/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/fresh_name.h"
#include "util/option_declarations.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/type_context.h"
#include "library/pp_options.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/cache_helper.h"
#include "library/module.h"
#include "library/check.h"
#include "library/aux_definition.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/tactic_evaluator.h"

namespace lean {
void tactic_state_cell::dealloc() {
    delete this;
}

tactic_state::tactic_state(environment const & env, options const & o, name const & decl_name, metavar_context const & ctx,
                           list<expr> const & gs, expr const & main) {
    m_ptr = new tactic_state_cell(env, o, decl_name, ctx, gs, main);
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
    return tactic_state(env, o, decl_name, mctx, list<expr>(main), main);
}

tactic_state mk_tactic_state_for(environment const & env, options const & o, name const & decl_name,
                                 local_context const & lctx, expr const & type) {
    return mk_tactic_state_for(env, o, decl_name, metavar_context(), lctx, type);
}

tactic_state mk_tactic_state_for_metavar(environment const & env, options const & opts, name const & decl_name,
                                         metavar_context const & mctx, expr const & mvar) {
    return tactic_state(env, opts, decl_name, mctx, list<expr>(mvar), mvar);
}

tactic_state set_options(tactic_state const & s, options const & o) {
    return tactic_state(s.env(), o, s.decl_name(), s.mctx(), s.goals(), s.main());
}

tactic_state set_env(tactic_state const & s, environment const & env) {
    return tactic_state(env, s.get_options(), s.decl_name(), s.mctx(), s.goals(), s.main());
}

tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx) {
    return tactic_state(s.env(), s.get_options(), s.decl_name(), mctx, s.goals(), s.main());
}

tactic_state set_env_mctx(tactic_state const & s, environment const & env, metavar_context const & mctx) {
    return tactic_state(env, s.get_options(), s.decl_name(), mctx, s.goals(), s.main());
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
                        s.main());
}

tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), s.decl_name(), mctx, consume_solved_prefix(mctx, gs), s.main());
}

tactic_state set_env_mctx_goals(tactic_state const & s, environment const & env,
                                metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(env, s.get_options(), s.decl_name(), mctx, consume_solved_prefix(mctx, gs),
                        s.main());
}

tactic_state set_mctx_lctx(tactic_state const & s, metavar_context const & mctx, local_context const & lctx) {
    metavar_context new_mctx = mctx;
    expr mvar = new_mctx.mk_metavar_decl(lctx, mk_true());
    return tactic_state(s.env(), s.get_options(), s.decl_name(), new_mctx, to_list(mvar), mvar);
}

format tactic_state::pp_expr(formatter_factory const & fmtf, expr const & e) const {
    type_context_old ctx = mk_cacheless_type_context_for(*this, transparency_mode::All);
    formatter fmt = fmtf(env(), get_options(), ctx);
    return fmt(e);
}

format tactic_state::pp_goal(formatter_factory const & fmtf, expr const & g, bool /* target_lhs_only */) const {
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
    r                         += lctx.pp(fmt);
    unsigned indent            = get_pp_indent(get_options());
    bool unicode               = get_pp_unicode(get_options());
    if (!lctx.empty())
        r += line();
    expr type                  = decl.get_type();
    if (inst_mvars)
        type                   = mctx_tmp.instantiate_mvars(type);
    expr rel, lhs, rhs;
    format turnstile(unicode ? "⊢" : "|-");
    r += turnstile + space() + nest(indent, fmt(type));
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

type_context_old mk_cacheless_type_context_for(tactic_state const & s, transparency_mode m) {
    return mk_type_context_for(s, m);
}

format tactic_state::pp() const {
    return pp_core();
}

void initialize_tactic_state() {
}

void finalize_tactic_state() {
}
}

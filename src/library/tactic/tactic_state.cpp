/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
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
#include "library/vm/vm_format.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_io.h"
#include "library/vm/interaction_state_imp.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/tactic_evaluator.h"

namespace lean {
/* is_ts_safe is required by the interaction_state implementation. */
template struct interaction_monad<tactic_state>;

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
    if (is_eqp(s.mctx(), mctx)) return s;
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
    if (is_eqp(s.mctx(), mctx)) {
        optional<metavar_decl> mdecl = s.get_main_goal_decl();
        if (mdecl && is_decl_eqp(mdecl->get_context(), lctx))
            return s;
    }
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

vm_obj to_obj(tactic_state const & s) {
    return tactic::to_obj(s);
}

transparency_mode to_transparency_mode(vm_obj const & o) {
    return static_cast<transparency_mode>(cidx(o));
}

vm_obj to_obj(transparency_mode m) {
    return mk_vm_simple(static_cast<unsigned>(m));
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

vm_obj mk_no_goals_exception(tactic_state const & s) {
    return tactic::mk_exception("tactic failed, there are no goals to be solved", s);
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
            bool is_meta         = true;
            name pp_name("_pp_tactic_state");
            new_env              = new_env.add(mk_definition(new_env, pp_name, {}, type, code, is_meta));
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

vm_obj tactic_unsafe_run_io(vm_obj const &, vm_obj const & a, vm_obj const & s) {
    return tactic::mk_success(run_io(a), s);
}

vm_obj io_run_tactic(vm_obj const &, vm_obj const & tac, vm_obj const &) {
    vm_state & vm  = get_vm_state();
    tactic_state s = mk_tactic_state_for(vm.env(), vm.get_options(), "_io_run_tactic",
                                         metavar_context(), local_context(), mk_true());
    vm_obj r = invoke(tac, to_obj(s));
    if (auto ex = tactic::is_exception(vm, r))
        return mk_ioe_failure(to_obj(mk_tactic_error_msg(std::get<2>(*ex), std::get<0>(*ex))));
    else
        return mk_ioe_result(tactic::get_success_value(r));
}

void initialize_tactic_state() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "to_format"}),      tactic_state_to_format);
    DECLARE_VM_BUILTIN(name({"tactic", "format_result"}),        tactic_format_result);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe_run_io"}),        tactic_unsafe_run_io);
    DECLARE_VM_BUILTIN(name({"io", "run_tactic"}),               io_run_tactic);
}

void finalize_tactic_state() {
}
}

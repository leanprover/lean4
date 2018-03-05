/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/check.h"
#include "library/pp_options.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/occurrences.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/clear_tactic.h"
#include "library/tactic/assert_tactic.h"
#include "library/tactic/rewrite_tactic.h"

namespace lean {
rewrite_cfg::rewrite_cfg(vm_obj const & cfg):apply_cfg(cfield(cfg, 0)) {
    m_symm = to_bool(cfield(cfg, 1));
    m_occs = to_occurrences(cfield(cfg, 2));
}

static vm_obj rewrite_core(expr h, expr e, rewrite_cfg const & cfg, tactic_state s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context(cfg.m_mode);
    type_context_old::approximate_scope _(ctx, cfg.m_approx);
    expr h_type      = ctx.infer(h);
    /* Generate meta-variables for arguments */
    buffer<expr> metas;
    buffer<bool> is_instance;
    while (true) {
        h_type    = ctx.relaxed_try_to_pi(h_type);
        if (!is_pi(h_type))
            break;
        expr meta = ctx.mk_metavar_decl(ctx.lctx(), binding_domain(h_type));
        is_instance.push_back(binding_info(h_type).is_inst_implicit());
        metas.push_back(meta);
        h          = mk_app(h, meta);
        h_type     = instantiate(binding_body(h_type), meta);
    }
    expr A, lhs, rhs;
    if (is_iff(h_type, lhs, rhs)) {
        h      = mk_app(mk_constant(get_propext_name()), lhs, rhs, h);
        h_type = mk_eq(ctx, lhs, rhs);
    }
    h_type = annotated_head_beta_reduce(h_type);
    if (!is_eq(h_type, A, lhs, rhs))
        return tactic::mk_exception("rewrite tactic failed, lemma is not an equality nor a iff", s);
    if (is_metavar(lhs))
        return tactic::mk_exception("rewrite tactic failed, lemma lhs is a metavariable", s);
    if (cfg.m_symm) {
        h      = mk_eq_symm(ctx, h);
        h_type = mk_eq(ctx, rhs, lhs);
        std::swap(lhs, rhs);
    }
    e = ctx.instantiate_mvars(e);
    expr pattern = lhs;
    lean_trace("rewrite", tout() << "before kabstract\n";);
    expr e_abst  = kabstract(ctx, e, pattern, cfg.m_occs, cfg.m_unify);
    if (closed(e_abst)) {
        auto new_s = update_option_if_undef(s, get_pp_beta_name(), false);
        auto thunk = [=]() {
            format msg = format("rewrite tactic failed, did not find instance of the pattern in the target expression");
            msg += pp_indented_expr(new_s, pattern);
            return msg;
        };
        return tactic::mk_exception(thunk, new_s);
    }
    /* Synthesize type class instances */
    vm_obj out_error_obj;
    if (cfg.m_instances && !synth_instances(ctx, metas, is_instance, s, &out_error_obj, "rewrite"))
        return out_error_obj;
    /* Collect unassigned mvars */
    buffer<expr> new_goals;
    collect_new_goals(ctx, cfg.m_new_goals, metas, new_goals);
    /* Motive and resulting type */
    expr new_e       = ctx.instantiate_mvars(instantiate(e_abst, rhs));
    expr e_eq_e      = mk_eq(ctx, e, e);
    expr e_eq_e_abst = mk_app(app_fn(e_eq_e), e_abst);
    expr motive = mk_lambda("_a", A, e_eq_e_abst);
    try {
        type_context_old::transparency_scope scope(ctx, ensure_semireducible_mode(ctx.mode()));
        check(ctx, motive);
    } catch (exception & ex) {
        throw nested_exception("rewrite tactic failed, motive is not type correct", ex);
    }
    expr prf           = mk_eq_rec(ctx, motive, mk_eq_refl(ctx, e), h);
    tactic_state new_s = set_mctx_goals(s, ctx.mctx(), append(cons(head(s.goals()), to_list(new_goals)), tail(s.goals())));
    return tactic::mk_success(mk_vm_pair(to_obj(new_e), mk_vm_pair(to_obj(prf), to_obj(to_list(metas)))), new_s);
}

vm_obj tactic_rewrite_core(vm_obj const & h, vm_obj const & e, vm_obj const & cfg, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    return rewrite_core(to_expr(h), to_expr(e), rewrite_cfg(cfg), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

void initialize_rewrite_tactic() {
    register_trace_class("rewrite");
    DECLARE_VM_BUILTIN(name({"tactic", "rewrite_core"}),    tactic_rewrite_core);
}

void finalize_rewrite_tactic() {
}
}

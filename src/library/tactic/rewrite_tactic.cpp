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

namespace lean {
vm_obj rewrite(transparency_mode const & m, bool approx, bool use_instances, occurrences const & occs, bool symm, expr H, optional<expr> const & target, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context ctx = mk_type_context_for(s, m);
    type_context::approximate_scope _(ctx, approx);
    expr H_type      = ctx.infer(H);
    /* Generate meta-variables for arguments */
    buffer<expr> metas;
    buffer<bool> is_instance;
    while (true) {
        H_type    = ctx.relaxed_try_to_pi(H_type);
        if (!is_pi(H_type))
            break;
        expr meta = ctx.mk_metavar_decl(ctx.lctx(), binding_domain(H_type));
        is_instance.push_back(binding_info(H_type).is_inst_implicit());
        metas.push_back(meta);
        H          = mk_app(H, meta);
        H_type     = instantiate(binding_body(H_type), meta);
    }
    expr A, lhs, rhs;
    if (is_iff(H_type, lhs, rhs)) {
        H      = mk_app(mk_constant(get_propext_name()), lhs, rhs, H);
        H_type = mk_eq(ctx, lhs, rhs);
    }
    H_type = annotated_head_beta_reduce(H_type);
    if (!is_eq(H_type, A, lhs, rhs))
        return tactic::mk_exception("rewrite tactic failed, lemma is not an equality nor a iff", s);
    if (is_metavar(lhs))
        return tactic::mk_exception("rewrite tactic failed, lemma lhs is a metavariable", s);
    if (!target)
        symm = !symm;
    if (symm) {
        H      = mk_eq_symm(ctx, H);
        H_type = mk_eq(ctx, rhs, lhs);
        std::swap(lhs, rhs);
    }
    expr e;
    if (target)
        e = ctx.infer(*target);
    else
        e = g->get_type();
    expr pattern = target ? lhs : rhs;
    lean_trace("rewrite", tout() << "before kabstract\n";);
    expr e_abst  = kabstract(ctx, e, pattern, occs);
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
    if (use_instances) {
        unsigned i = is_instance.size();
        while (i > 0) {
            --i;
            if (!is_instance[i]) continue;
            expr const & meta   = metas[i];
            if (ctx.is_assigned(meta)) continue;
            expr meta_type      = ctx.instantiate_mvars(ctx.infer(meta));
            optional<expr> inst = ctx.mk_class_instance(meta_type);
            if (!inst) {
                return tactic::mk_exception(sstream() << "rewrite tactic failed, failed to synthesize type class instance for #"
                                           << (i+1) << " argument", s);
            }
            if (!ctx.is_def_eq(meta, *inst)) {
                return tactic::mk_exception(sstream() << "rewrite tactic failed, failed to assign type class instance for #"
                                           << (i+1) << " argument", s);
            }
        }
    }
    /* Collect unassigned mvars */
    buffer<expr> unassigned_mvars;
    for (expr const & mvar : metas) {
        if (!ctx.is_assigned(mvar)) {
            ctx.instantiate_mvars_at_type_of(mvar);
            unassigned_mvars.push_back(mvar);
        }
    }
    /* Motive and resulting type */
    expr new_e  = ctx.instantiate_mvars(instantiate(e_abst, target ? rhs : lhs));
    expr motive = mk_lambda("a", A, e_abst);
    try {
        check(ctx, motive);
    } catch (exception & ex) {
        throw nested_exception("rewrite tactic failed, motive is not type correct", ex);
    }
    if (target) {
        expr prf        = mk_eq_rec(ctx, motive, *target, H);
        name Hname      = is_local(*target) ? local_pp_name(*target) : name("H");
        tactic_state s1 = set_mctx_goals(s, ctx.mctx(), cons(head(s.goals()), append(to_list(unassigned_mvars), tail(s.goals()))));
        vm_obj r2       = assertv_definev(true, Hname, new_e, prf, s1);
        if (optional<tactic_state> const & s2 = tactic::is_success(r2)) {
            if (is_local(*target)) {
                /* Try to clear target */
                vm_obj r3   = clear_internal(mlocal_name(*target), *s2);
                if (tactic::is_success(r3))
                    return r3;
            }
            return r2;
        } else {
            return tactic::mk_exception(sstream() << "rewrite tactic failed, failed to create new hypothesis", s);
        }
    } else {
        expr new_mvar = ctx.mk_metavar_decl(ctx.lctx(), new_e);
        expr prf      = mk_eq_rec(ctx, motive, new_mvar, H);
        ctx.assign(head(s.goals()), prf);
        return tactic::mk_success(set_mctx_goals(s, ctx.mctx(), cons(new_mvar, append(to_list(unassigned_mvars), tail(s.goals())))));
    }
}

vm_obj tactic_rewrite(vm_obj const & m, vm_obj const & approx, vm_obj const & use_instances, vm_obj const & occs, vm_obj const & symm, vm_obj const & H, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    return rewrite(to_transparency_mode(m), to_bool(approx), to_bool(use_instances),
                   to_occurrences(occs), to_bool(symm), to_expr(H), none_expr(), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

vm_obj tactic_rewrite_at(vm_obj const & m, vm_obj const & approx, vm_obj const & use_instances,
                         vm_obj const & occs, vm_obj const & symm, vm_obj const & H1, vm_obj const & H2, vm_obj const & s) {
    LEAN_TACTIC_TRY;
    return rewrite(to_transparency_mode(m), to_bool(approx), to_bool(use_instances), to_occurrences(occs),
                   to_bool(symm), to_expr(H1), some_expr(to_expr(H2)), tactic::to_state(s));
    LEAN_TACTIC_CATCH(tactic::to_state(s));
}

void initialize_rewrite_tactic() {
    register_trace_class("rewrite");
    DECLARE_VM_BUILTIN(name({"tactic", "rewrite_core"}),    tactic_rewrite);
    DECLARE_VM_BUILTIN(name({"tactic", "rewrite_at_core"}), tactic_rewrite_at);
}

void finalize_rewrite_tactic() {
}
}

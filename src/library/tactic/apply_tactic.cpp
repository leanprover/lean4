/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
static unsigned get_expect_num_args(type_context & ctx, expr e) {
    type_context::tmp_locals locals(ctx);
    unsigned r = 0;
    while (true) {
        e = ctx.relaxed_whnf(e);
        if (!is_pi(e))
            return r;
        // TODO(Leo): try to avoid the following instantiate.
        expr local = locals.push_local(binding_name(e), binding_domain(e), binding_info(e));
        e = instantiate(binding_body(e), local);
        r++;
    }
}

/** \brief Given a sequence metas/goals: <tt>(?m_1 ...) (?m_2 ... ) ... (?m_k ...)</tt>,
    we say ?m_i is "redundant" if it occurs in the type of some ?m_j.
    This procedure removes from metas any redundant element. */
static void remove_redundant_goals(metavar_context & mctx, buffer<expr> & metas) {
    unsigned k = 0;
    for (unsigned i = 0; i < metas.size(); i++) {
        bool found = false;
        for (unsigned j = 0; j < metas.size(); j++) {
            if (j != i) {
                if (occurs(metas[i], mctx.get_metavar_decl(metas[j])->get_type())) {
                    found = true;
                    break;
                }
            }
        }
        if (!found) {
            metas[k] = metas[i];
            k++;
        }
    }
    metas.shrink(k);
}

/* If out_error_obj is not nullptr, we store an the error message there when result is none */
optional<tactic_state> apply_core(type_context & ctx, bool add_all, bool use_instances, vm_obj * out_error_obj,
                                  expr e, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    lean_assert(g);
    local_context lctx   = g->get_context();
    expr target          = g->get_type();
    expr e_type          = ctx.infer(e);
    unsigned num_e_t     = get_expect_num_args(ctx, e_type);
    unsigned num_t       = get_expect_num_args(ctx, target);
    if (num_t <= num_e_t)
        num_e_t -= num_t;
    else
        num_e_t = 0;
    /* Generate meta-variables for arguments */
    buffer<expr> metas;
    buffer<bool> is_instance;
    for (unsigned i = 0; i < num_e_t; i++) {
        e_type    = ctx.relaxed_whnf(e_type);
        expr meta = ctx.mk_metavar_decl(lctx, binding_domain(e_type));
        is_instance.push_back(binding_info(e_type).is_inst_implicit());
        metas.push_back(meta);
        e          = mk_app(e, meta);
        e_type     = instantiate(binding_body(e_type), meta);
    }
    /* Unify */
    lean_assert(metas.size() == is_instance.size());
    if (!ctx.is_def_eq(target, e_type)) {
        if (out_error_obj) {
            auto thunk = [=]() {
                format msg = format("invalid apply tactic, failed to unify");
                msg += pp_indented_expr(s, target);
                msg += line() + format("with");
                msg += pp_indented_expr(s, e_type);
                return msg;
            };
            *out_error_obj = mk_tactic_exception(thunk, s);
        }
        return none_tactic_state();
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
                if (out_error_obj) {
                    auto thunk = [=]() {
                        format msg("invalid apply tactic, failed to synthesize type class instance for #");
                        msg += format(i+1);
                        msg += space() + format("argument");
                        return msg;
                    };
                    *out_error_obj = mk_tactic_exception(thunk, s);
                }
                return none_tactic_state();
            }
            if (!ctx.is_def_eq(meta, *inst)) {
                if (out_error_obj) {
                    auto thunk = [=]() {
                        format msg("invalid apply tactic, failed to assign type class instance for #");
                        msg += format(i+1);
                        msg += space() + format("argument");
                        return msg;
                    };
                    *out_error_obj = mk_tactic_exception(thunk, s);
                }
                return none_tactic_state();
            }
        }
    }
    /* Collect unassigned meta-variables */
    buffer<expr> new_goals;
    for (auto m : metas) {
        if (!ctx.is_assigned(m)) {
            ctx.instantiate_mvars_at_type_of(m);
            new_goals.push_back(m);
        }
    }
    metavar_context mctx = ctx.mctx();
    if (!add_all)
        remove_redundant_goals(mctx, new_goals);
    /* Assign, and create new tactic_state */
    e = mctx.instantiate_mvars(e);
    mctx.assign(head(s.goals()), e);
    return some_tactic_state(set_mctx_goals(s, mctx,
                                            to_list(new_goals.begin(), new_goals.end(), tail(s.goals()))));
}

optional<tactic_state> apply(type_context & ctx, bool add_all, bool use_instances, expr const & e, tactic_state const & s) {
    return apply_core(ctx, add_all, use_instances, nullptr, e, s);
}

vm_obj apply_core(transparency_mode md, bool approx, bool add_all, bool use_instances, expr e, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context ctx = mk_type_context_for(s, md);
    type_context::approximate_scope _(ctx, approx);
    try {
        vm_obj error_obj;
        optional<tactic_state> new_s = apply_core(ctx, add_all, use_instances, &error_obj, e, s);
        if (!new_s)
            return error_obj;
        return mk_tactic_success(*new_s);
    } catch(exception & ex) {
        return mk_tactic_exception(ex, s);
    }
}

vm_obj tactic_apply_core(vm_obj const & md, vm_obj const & approx, vm_obj const & all, vm_obj const & insts, vm_obj const & e, vm_obj const & s) {
    return apply_core(static_cast<transparency_mode>(cidx(md)), to_bool(approx), to_bool(all), to_bool(insts), to_expr(e), to_tactic_state(s));
}

void initialize_apply_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "apply_core"}),   tactic_apply_core);
}

void finalize_apply_tactic() {
}
}

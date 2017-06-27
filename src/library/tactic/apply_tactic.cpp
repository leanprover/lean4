/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
new_goals_kind to_new_goals_kind(vm_obj const & k) {
    switch (cidx(k)) {
    case 0:  return new_goals_kind::NonDepFirst;
    case 1:  return new_goals_kind::NonDepOnly;
    default: return new_goals_kind::All;
    }
}

apply_cfg::apply_cfg(vm_obj const & cfg):
    m_mode(to_transparency_mode(cfield(cfg, 0))),
    m_approx(to_bool(cfield(cfg, 1))),
    m_new_goals(to_new_goals_kind(cfield(cfg, 2))),
    m_instances(to_bool(cfield(cfg, 3))),
    m_auto_param(to_bool(cfield(cfg, 4))),
    m_opt_param(to_bool(cfield(cfg, 5))) {
}

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

bool try_instance(type_context & ctx, expr const & meta, tactic_state const & s, vm_obj * out_error_obj, char const * tac_name) {
    if (ctx.is_assigned(meta))
        return true;
    expr meta_type      = ctx.instantiate_mvars(ctx.infer(meta));
    optional<expr> inst = ctx.mk_class_instance(meta_type);
    if (!inst) {
        if (out_error_obj) {
            auto thunk = [=]() {
                format msg("invalid");
                msg += space() + format(tac_name) + space();
                msg += format("tactic, failed to synthesize type class instance");
                return msg;
            };
            *out_error_obj = tactic::mk_exception(thunk, s);
        }
        return false;
    }
    if (!ctx.is_def_eq(meta, *inst)) {
        if (out_error_obj) {
            auto thunk = [=]() {
                format msg("invalid");
                msg += space() + format(tac_name) + space();
                msg += format("tactic, failed to assign type class instance");
                return msg;
            };
            *out_error_obj = tactic::mk_exception(thunk, s);
        }
        return false;
    }
    return true;
}

bool try_auto_param(type_context & /* ctx */, expr const & /* meta */,
                    tactic_state const & /* s */, vm_obj * /* out_error_obj */, char const * /* tac_name */) {
    // TODO(Leo)
    return true;
}

bool try_opt_param(type_context & /* ctx */, expr const & /* meta */,
                   tactic_state const & /* s */, vm_obj * /* out_error_obj */, char const * /* tac_name */) {
    // TODO(Leo)
    return true;
}

/** \brief Given a sequence metas/goals: <tt>(?m_1 ...) (?m_2 ... ) ... (?m_k ...)</tt>,
    we say ?m_i is "redundant" if it occurs in the type of some ?m_j.
    This procedure removes from metas any redundant element. */
void remove_dep_goals(type_context & ctx, buffer<expr> & metas) {
    unsigned k = 0;
    for (unsigned i = 0; i < metas.size(); i++) {
        bool found = false;
        for (unsigned j = 0; j < metas.size(); j++) {
            if (j != i) {
                if (occurs(metas[i], ctx.infer(metas[j]))) {
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

void reorder_non_dep_first(type_context & ctx, buffer<expr> & metas) {
    buffer<expr> non_dep, dep;
    for (unsigned i = 0; i < metas.size(); i++) {
        bool found = false;
        for (unsigned j = 0; j < metas.size(); j++) {
            if (j != i) {
                if (occurs(metas[i], ctx.infer(metas[j]))) {
                    found = true;
                    break;
                }
            }
        }
        if (found) {
            dep.push_back(metas[i]);
        } else {
            non_dep.push_back(metas[i]);
        }
    }
    metas.clear();
    metas.append(non_dep);
    metas.append(dep);
}

static optional<tactic_state> apply(type_context & ctx, expr e, apply_cfg const & cfg, tactic_state const & s,
                                    vm_obj * out_error_obj, list<expr> * new_metas) {
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
    if (!ctx.is_def_eq(e_type, target)) {
        if (out_error_obj) {
            auto thunk = [=]() {
                format msg = format("invalid apply tactic, failed to unify");
                msg += pp_indented_expr(s, target);
                msg += line() + format("with");
                msg += pp_indented_expr(s, e_type);
                return msg;
            };
            *out_error_obj = tactic::mk_exception(thunk, s);
        }
        return none_tactic_state();
    }
    /* Synthesize type class instances */
    if (cfg.m_instances) {
        unsigned i = is_instance.size();
        while (i > 0) {
            --i;
            if (!is_instance[i]) continue;
            if (!try_instance(ctx, metas[i], s, out_error_obj, "apply"))
                return none_tactic_state();
        }
    }
    /* Synthesize using auto_param and opt_param */
    if (cfg.m_opt_param || cfg.m_auto_param) {
        unsigned i = metas.size();
        while (i > 0) {
            --i;
            if (cfg.m_opt_param && !try_opt_param(ctx, metas[i], s, out_error_obj, "apply"))
                return none_tactic_state();
            if (cfg.m_auto_param && !try_auto_param(ctx, metas[i], s, out_error_obj, "apply"))
                return none_tactic_state();
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
    switch (cfg.m_new_goals) {
    case new_goals_kind::NonDepFirst:
        reorder_non_dep_first(ctx, new_goals);
        break;
    case new_goals_kind::NonDepOnly:
        remove_dep_goals(ctx, new_goals);
        break;
    case new_goals_kind::All:
        break; /* do nothing */
    }
    metavar_context mctx = ctx.mctx();
    /* Assign, and create new tactic_state */
    e = mctx.instantiate_mvars(e);
    mctx.assign(head(s.goals()), e);
    if (new_metas) *new_metas = to_list(metas);
    return some_tactic_state(set_mctx_goals(s, mctx,
                                            to_list(new_goals.begin(), new_goals.end(), tail(s.goals()))));
}

optional<tactic_state> apply(type_context & ctx, expr const & e, apply_cfg const & cfg, tactic_state const & s) {
    return apply(ctx, e, cfg, s, nullptr, nullptr);
}

optional<tactic_state> apply(type_context & ctx, bool all, bool use_instances, expr const & e, tactic_state const & s) {
    apply_cfg cfg;
    cfg.m_new_goals     = all ? new_goals_kind::All : new_goals_kind::NonDepOnly;
    cfg.m_instances     = use_instances;
    return apply(ctx, e, cfg, s, nullptr, nullptr);
}

vm_obj tactic_apply_core(vm_obj const & e, vm_obj const & cfg0, vm_obj const & s0) {
    tactic_state const & s = tactic::to_state(s0);
    apply_cfg cfg(cfg0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context ctx = mk_type_context_for(s, cfg.m_mode);
    type_context::approximate_scope _(ctx, cfg.m_approx);
    try {
        vm_obj error_obj;
        list<expr> new_metas;
        optional<tactic_state> new_s = apply(ctx, to_expr(e), cfg, s, &error_obj, &new_metas);
        if (!new_s)
            return error_obj;
        return tactic::mk_success(to_obj(new_metas), *new_s);
    } catch(exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_apply_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "apply_core"}),   tactic_apply_core);
}

void finalize_apply_tactic() {
}
}

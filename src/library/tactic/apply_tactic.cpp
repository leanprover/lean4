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
#include "library/vm/vm_name.h"
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
    m_opt_param(to_bool(cfield(cfg, 5))),
    m_unify(to_bool(cfield(cfg, 6))) {
}

/*
  Compute the number of expected arguments and whether the result type is of the form
  (?m ...) where ?m is an unassigned metavariable.
*/
static pair<unsigned, bool> get_expected_num_args_ho_result(type_context_old & ctx, expr e) {
    type_context_old::tmp_locals locals(ctx);
    unsigned r = 0;
    while (true) {
        e = ctx.relaxed_whnf(e);
        if (!is_pi(e)) {
            expr fn = get_app_fn(e);
            bool ho_result = is_metavar(fn) && !ctx.is_assigned(fn);
            return mk_pair(r, ho_result);
        }
        // TODO(Leo): try to avoid the following instantiate.
        expr local = locals.push_local(binding_name(e), binding_domain(e), binding_info(e));
        e = instantiate(binding_body(e), local);
        r++;
    }
}

static unsigned get_expected_num_args(type_context_old & ctx, expr e) {
    return get_expected_num_args_ho_result(ctx, e).first;
}

static bool try_instance(type_context_old & ctx, expr const & meta, tactic_state const & s, vm_obj * out_error_obj, char const * tac_name) {
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

bool synth_instances(type_context_old & ctx, buffer<expr> const & metas, buffer<bool> const & is_instance,
                     tactic_state const & s, vm_obj * out_error_obj, char const * tac_name) {
    unsigned i = is_instance.size();
    while (i > 0) {
        --i;
        if (!is_instance[i]) continue;
        if (!try_instance(ctx, metas[i], s, out_error_obj, tac_name))
            return false;
    }
    return true;
}

/** \brief Given a sequence metas/goals: <tt>(?m_1 ...) (?m_2 ... ) ... (?m_k ...)</tt>,
    we say ?m_i is "redundant" if it occurs in the type of some ?m_j.
    This procedure removes from metas any redundant element. */
static void remove_dep_goals(type_context_old & ctx, buffer<expr> & metas) {
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

static void reorder_non_dep_first(type_context_old & ctx, buffer<expr> & metas) {
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

void collect_new_goals(type_context_old & ctx, new_goals_kind k, buffer<expr> const & metas, buffer<expr> & new_goals) {
    for (auto m : metas) {
        if (!ctx.is_assigned(m)) {
            ctx.instantiate_mvars_at_type_of(m);
            new_goals.push_back(m);
        }
    }
    switch (k) {
    case new_goals_kind::NonDepFirst:
        reorder_non_dep_first(ctx, new_goals);
        break;
    case new_goals_kind::NonDepOnly:
        remove_dep_goals(ctx, new_goals);
        break;
    case new_goals_kind::All:
        break; /* do nothing */
    }
}

static optional<tactic_state> apply(type_context_old & ctx, expr e, apply_cfg const & cfg, tactic_state const & s,
                                    vm_obj * out_error_obj, vm_obj * new_metas) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    lean_assert(g);
    local_context lctx   = g->get_context();
    expr target          = g->get_type();
    expr e_type          = ctx.infer(e);
    unsigned num_e_t; bool ho_result;
    std::tie(num_e_t, ho_result) = get_expected_num_args_ho_result(ctx, e_type);
    if (!ho_result) {
        /* Result type is not of the form `(?m ...)` */
        unsigned num_t = get_expected_num_args(ctx, target);
        if (num_t <= num_e_t)
            num_e_t -= num_t;
        else
            num_e_t = 0;
    }
    /* Generate meta-variables for arguments */
    buffer<expr> metas;
    buffer<name> meta_names;
    buffer<bool> is_instance;
    for (unsigned i = 0; i < num_e_t; i++) {
        e_type    = ctx.relaxed_whnf(e_type);
        expr meta = ctx.mk_metavar_decl(lctx, binding_domain(e_type));
        is_instance.push_back(binding_info(e_type).is_inst_implicit());
        metas.push_back(meta);
        meta_names.push_back(binding_name(e_type));
        e          = mk_app(e, meta);
        e_type     = instantiate(binding_body(e_type), meta);
    }
    /* Unify */
    lean_assert(metas.size() == is_instance.size());

    if ((cfg.m_unify && !ctx.unify(e_type, target)) ||
        (!cfg.m_unify && !ctx.match(e_type, target))) {
        if (out_error_obj) {
            auto pp_ctx = ::lean::mk_pp_ctx(ctx.env(), s.get_options(), ctx.mctx(), ctx.lctx());
            auto thunk = [=]() {
                format msg = format("invalid apply tactic, failed to ");
                if (cfg.m_unify)
                    msg += format("unify");
                else
                    msg += format("match");
                unsigned i = get_pp_indent(s.get_options());
                msg += nest(i, line() + pp_ctx(target));
                msg += line() + format("with");
                msg += nest(i, line() + pp_ctx(e_type));
                return msg;
            };
            *out_error_obj = tactic::mk_exception(thunk, s);
        }
        return none_tactic_state();
    }
    /* Synthesize type class instances */
    if (cfg.m_instances && !synth_instances(ctx, metas, is_instance, s, out_error_obj, "apply"))
        return none_tactic_state();
    /* Collect unassigned meta-variables */
    buffer<expr> new_goals;
    collect_new_goals(ctx, cfg.m_new_goals, metas, new_goals);
    metavar_context mctx = ctx.mctx();
    /* Assign, and create new tactic_state */
    e = mctx.instantiate_mvars(e);
    mctx.assign(head(s.goals()), e);
    if (new_metas) {
        lean_assert(metas.size() == meta_names.size());
        *new_metas = mk_vm_nil();
        unsigned i = meta_names.size();
        while (i > 0) {
            --i;
            *new_metas = mk_vm_cons(mk_vm_pair(to_obj(meta_names[i]), to_obj(metas[i])), *new_metas);
        }
    }
    return some_tactic_state(set_mctx_goals(s, mctx,
                                            to_list(new_goals.begin(), new_goals.end(), tail(s.goals()))));
}

optional<tactic_state> apply(type_context_old & ctx, expr const & e, apply_cfg const & cfg, tactic_state const & s) {
    return apply(ctx, e, cfg, s, nullptr, nullptr);
}

optional<tactic_state> apply(type_context_old & ctx, bool all, bool use_instances, expr const & e, tactic_state const & s) {
    apply_cfg cfg;
    cfg.m_new_goals     = all ? new_goals_kind::All : new_goals_kind::NonDepOnly;
    cfg.m_instances     = use_instances;
    return apply(ctx, e, cfg, s, nullptr, nullptr);
}

vm_obj tactic_apply_core(vm_obj const & e, vm_obj const & cfg0, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    apply_cfg cfg(cfg0);
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context(cfg.m_mode);
    type_context_old::approximate_scope _(ctx, cfg.m_approx);
    try {
        vm_obj error_obj;
        vm_obj new_metas;
        optional<tactic_state> new_s = apply(ctx, to_expr(e), cfg, s, &error_obj, &new_metas);
        if (!new_s)
            return error_obj;
        return tactic::mk_success(new_metas, *new_s);
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

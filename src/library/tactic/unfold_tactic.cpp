/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/type_context.h"
#include "library/util.h"
#include "library/trace.h"
#include "library/constants.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_list.h"
#include "library/tactic/eqn_lemmas.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/occurrences.h"
#include "library/tactic/dsimplify.h"

namespace lean {
vm_obj tactic_unfold_projection(vm_obj const & _e, vm_obj const & m, vm_obj const & _s) {
    expr const & e = to_expr(_e);
    tactic_state const & s = tactic::to_state(_s);
    try {
        expr const & fn = get_app_fn(e);
        type_context_old ctx = mk_type_context_for(s, to_transparency_mode(m));
        if (!is_constant(fn) || !is_projection(s.env(), const_name(fn)))
            return tactic::mk_exception("unfold projection failed, expression is not a projection application", s);
        if (auto new_e = ctx.reduce_projection(e))
            return tactic::mk_success(to_obj(*new_e), s);
        return tactic::mk_exception("unfold projection failed, failed to unfold", s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

optional<expr> dunfold(type_context_old & ctx, expr const & e) {
    environment const & env = ctx.env();
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return none_expr();
    buffer<simp_lemma> lemmas;
    bool refl_only = true;
    get_eqn_lemmas_for(env, const_name(fn), refl_only, lemmas);

    expr it = e;
    buffer<expr> extra_args;
    while (true) {
        for (simp_lemma const & sl : lemmas) {
            expr new_it = refl_lemma_rewrite(ctx, it, sl);
            if (new_it != it) {
                expr new_e = annotated_head_beta_reduce(mk_rev_app(new_it, extra_args));
                return some_expr(new_e);
            }
        }
        if (!is_app(it))
            return none_expr();
        extra_args.push_back(app_arg(it));
        it = app_fn(it);
    }
}

class unfold_core_fn : public dsimplify_core_fn {
protected:
    name_set    m_cs;

    static optional<pair<expr, bool>> none() {
        return optional<pair<expr, bool>>();
    }

    virtual bool check_occ() { return true; }

    optional<pair<expr, bool>> unfold_step(expr const & e) {
        if (!is_app(e) && !is_constant(e))
            return none();
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn) || !m_cs.contains(const_name(fn)))
            return none();
        type_context_old::transparency_scope scope(m_ctx, transparency_mode::Instances);
        optional<expr> new_e;
        if (is_projection(m_ctx.env(), const_name(fn))) {
            new_e = m_ctx.reduce_projection(e);
        } else if (has_eqn_lemmas(m_ctx.env(), const_name(fn))) {
            new_e = dunfold(m_ctx, e);
        } else {
            new_e = unfold_term(m_ctx.env(), e);
        }
        if (!new_e)
            return none();
        if (!check_occ())
            return none();
        return optional<pair<expr, bool>>(*new_e, !m_cfg.m_single_pass);
    }

public:
    unfold_core_fn(type_context_old & ctx, defeq_canonizer::state & dcs, list<name> const & cs, dsimp_config const & cfg):
        dsimplify_core_fn(ctx, dcs, cfg),
        m_cs(to_name_set(cs)) {
        m_cfg.m_zeta = false;
    }
};

class unfold_fn : public unfold_core_fn {
    virtual optional<pair<expr, bool>> post(expr const & e) override {
        return unfold_step(e);
    }
public:
    unfold_fn(type_context_old & ctx, defeq_canonizer::state & dcs, list<name> const & cs, dsimp_config const & cfg):
        unfold_core_fn(ctx, dcs, cs, cfg) {
    }
};

vm_obj tactic_dunfold(vm_obj const & cs, vm_obj const & _e, vm_obj const & _cfg, vm_obj const & _s) {
    expr const & e         = to_expr(_e);
    tactic_state const & s = tactic::to_state(_s);
    defeq_can_state dcs    = s.dcs();
    /*
       structure dunfold_config extends dsimp_config :=
       (md := transparency.instances) -- this is not a new field.
    */
    dsimp_config cfg(_cfg);
    type_context_old ctx       = mk_type_context_for(s, cfg.m_md);
    unfold_fn F(ctx, dcs, to_list_name(cs), cfg);
    try {
        expr new_e         = F(e);
        tactic_state new_s = set_mctx_dcs(s, F.mctx(), dcs);
        if (cfg.m_fail_if_unchanged && e == new_e) {
            return tactic::mk_exception("dunfold tactic failed to unfold", s);
        } else {
            return tactic::mk_success(to_obj(new_e), new_s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

vm_obj tactic_dunfold_head(vm_obj const & _e, vm_obj const & m, vm_obj const & _s) {
    expr const & e = to_expr(_e);
    tactic_state const & s = tactic::to_state(_s);
    try {
        environment const & env = s.env();
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return tactic::mk_exception("dunfold_expr failed, expression is not a constant nor a constant application", s);
        if (is_projection(s.env(), const_name(fn))) {
            type_context_old ctx = mk_type_context_for(s, to_transparency_mode(m));
            if (auto new_e = ctx.reduce_projection(e))
                return tactic::mk_success(to_obj(*new_e), s);
            return tactic::mk_exception("dunfold_expr failed, failed to unfold projection", s);
        } else if (has_eqn_lemmas(env, const_name(fn))) {
            type_context_old ctx = mk_type_context_for(s, to_transparency_mode(m));
            if (auto new_e = dunfold(ctx, e)) {
                return tactic::mk_success(to_obj(*new_e), s);
            } else {
                return tactic::mk_exception("dunfold_expr failed, none of the rfl lemmas is applicable", s);
            }
        } else if (auto new_e = unfold_term(env, e)) {
            return tactic::mk_success(to_obj(*new_e), s);
        } else {
            return tactic::mk_exception("dunfold_expr failed, failed to unfold", s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_unfold_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "unfold_proj"}),  tactic_unfold_projection);
    DECLARE_VM_BUILTIN(name({"tactic", "dunfold"}),      tactic_dunfold);
    DECLARE_VM_BUILTIN(name({"tactic", "dunfold_head"}), tactic_dunfold_head);
}

void finalize_unfold_tactic() {
}
}

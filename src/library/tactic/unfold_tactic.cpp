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
#include "library/tactic/eqn_lemmas.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/occurrences.h"

namespace lean {
vm_obj tactic_unfold_projection_core(vm_obj const & m, vm_obj const & _e, vm_obj const & _s) {
    expr const & e = to_expr(_e);
    tactic_state const & s = tactic::to_state(_s);
    try {
        expr const & fn = get_app_fn(e);
        type_context ctx = mk_type_context_for(s, to_transparency_mode(m));
        if (!is_constant(fn) || !is_projection(s.env(), const_name(fn)))
            return tactic::mk_exception("unfold projection failed, expression is not a projection application", s);
        if (auto new_e = ctx.reduce_projection(e))
            return tactic::mk_success(to_obj(*new_e), s);
        return tactic::mk_exception("unfold projection failed, failed to unfold", s);
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

optional<expr> dunfold(type_context & ctx, expr const & e) {
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

vm_obj tactic_dunfold_expr_core(vm_obj const & m, vm_obj const & _e, vm_obj const & _s) {
    expr const & e = to_expr(_e);
    tactic_state const & s = tactic::to_state(_s);
    try {
        environment const & env = s.env();
        expr const & fn = get_app_fn(e);
        if (!is_constant(fn))
            return tactic::mk_exception("dunfold_expr failed, expression is not a constant nor a constant application", s);
        if (is_projection(s.env(), const_name(fn))) {
            type_context ctx = mk_type_context_for(s, to_transparency_mode(m));
            if (auto new_e = ctx.reduce_projection(e))
                return tactic::mk_success(to_obj(*new_e), s);
            return tactic::mk_exception("dunfold_expr failed, failed to unfold projection", s);
        } else if (has_eqn_lemmas(env, const_name(fn))) {
            type_context ctx = mk_type_context_for(s, to_transparency_mode(m));
            if (auto new_e = dunfold(ctx, e)) {
                return tactic::mk_success(to_obj(*new_e), s);
            } else {
                return tactic::mk_exception("dunfold_expr failed, none of the rfl lemmas is applicable", s);
            }
        } else {
            declaration d = env.get(const_name(fn));
            if (!d.is_definition())
                return tactic::mk_exception(sstream() << "dunfold_expr failed, '" << d.get_name() << "' is not a definition", s);
            if (d.get_num_univ_params() != length(const_levels(fn)))
                return tactic::mk_exception("dunfold_expr failed, incorrect number of universe levels", s);
            buffer<expr> args;
            get_app_args(e, args);
            expr new_e = annotated_head_beta_reduce(mk_app(instantiate_value_univ_params(d, const_levels(fn)), args.size(), args.data()));
            return tactic::mk_success(to_obj(new_e), s);
        }
    } catch (exception & ex) {
        return tactic::mk_exception(ex, s);
    }
}

void initialize_unfold_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "unfold_projection_core"}), tactic_unfold_projection_core);
    DECLARE_VM_BUILTIN(name({"tactic", "dunfold_expr_core"}),      tactic_dunfold_expr_core);
}

void finalize_unfold_tactic() {
}
}

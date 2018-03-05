/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/util.h"
#include "library/delayed_abstraction.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
optional<expr> intron_core(environment const & env, options const & opts, metavar_context & mctx,
                           expr const & mvar, unsigned n, buffer<name> & new_Hns,
                           std::function<name(local_context const & lctx, name const & n)> const & mk_name) {
    lean_assert(is_metavar(mvar));
    optional<metavar_decl> g = mctx.find_metavar_decl(mvar);
    if (!g) return none_expr();
    type_context_old ctx     = mk_type_context_for(env, opts, mctx, g->get_context());
    expr type            = g->get_type();
    type_context_old::tmp_locals new_locals(ctx);
    buffer<expr> new_Hs;
    for (unsigned i = 0; i < n; i++) {
        if (!is_pi(type) && !is_let(type)) {
            type = ctx.whnf(type);
            if (!is_pi(type))
                return none_expr();
        }
        lean_assert(is_pi(type) || is_let(type));
        if (is_pi(type)) {
            name H_name = mk_name(ctx.lctx(), binding_name(type));
            expr H      = new_locals.push_local(H_name, annotated_head_beta_reduce(binding_domain(type)),
                                                binding_info(type));
            type        = instantiate(binding_body(type), H);
            new_Hs.push_back(H);
            new_Hns.push_back(mlocal_name(H));

        } else {
            lean_assert(is_let(type));
            name H_name = mk_name(ctx.lctx(), let_name(type));
            expr H      = new_locals.push_let(H_name, annotated_head_beta_reduce(let_type(type)), let_value(type));
            type        = instantiate(let_body(type), H);
            new_Hs.push_back(H);
            new_Hns.push_back(mlocal_name(H));
        }
    }
    expr new_M   = ctx.mk_metavar_decl(ctx.lctx(), type);
    expr new_val = abstract_locals(mk_delayed_abstraction_with_locals(new_M, new_Hs), new_Hs.size(), new_Hs.data());
    unsigned i   = new_Hs.size();
    while (i > 0) {
        --i;
        local_decl d = ctx.lctx().get_local_decl(new_Hs[i]);
        expr type = d.get_type();
        type      = abstract_locals(type, i, new_Hs.data());
        if (auto letval = d.get_value()) {
            letval    = abstract_locals(*letval, i, new_Hs.data());
            new_val   = mk_let(d.get_pp_name(), type, *letval, new_val);
        } else {
            new_val   = mk_lambda(d.get_pp_name(), type, new_val, d.get_info());
        }
    }
    lean_assert(!ctx.mctx().is_assigned(new_M));
    mctx = ctx.mctx();
    mctx.assign(mvar, new_val);
    return some_expr(new_M);
}

static name mk_aux_name(local_context const & lctx, list<name> & given_names, name const & default_name,
                        bool use_unused_names) {
    if (given_names) {
        name r      = head(given_names);
        given_names = tail(given_names);
        return r == "_" ? lctx.get_unused_name(default_name) : r;
    } else {
        return use_unused_names ? lctx.get_unused_name(default_name) : default_name;
    }
}

optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, list<name> & given_names, buffer<name> & new_Hns,
                      bool use_unused_names) {
    return intron_core(env, opts, mctx, mvar, n, new_Hns,
                       [&](local_context const & lctx, name const & n) {
                           return mk_aux_name(lctx, given_names, n, use_unused_names);
                       });
}

optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, list<name> & given_names, bool use_unused_names) {
    buffer<name> tmp;
    return intron(env, opts, mctx, mvar, n, given_names, tmp, use_unused_names);
}

optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, bool use_unused_names) {
    list<name> empty;
    return intron(env, opts, mctx, mvar, n, empty, use_unused_names);
}

optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, buffer<name> & new_Hns, bool use_unused_names) {
    list<name> empty;
    return intron(env, opts, mctx, mvar, n, empty, new_Hns, use_unused_names);
}

optional<tactic_state> intron(unsigned n, tactic_state const & s, buffer<name> & new_Hns, bool use_unused_names) {
    if (n == 0) return some_tactic_state(s);
    optional<expr> mvar  = s.get_main_goal();
    if (!mvar) return none_tactic_state();
    list<name> new_names;
    metavar_context mctx = s.mctx();
    if (optional<expr> new_M = intron(s.env(), s.get_options(), mctx, *mvar, n, new_names, new_Hns, use_unused_names)) {
        list<expr> new_gs(*new_M, tail(s.goals()));
        return some_tactic_state(set_mctx_goals(s, mctx, new_gs));
    } else {
        return none_tactic_state();
    }
}

optional<tactic_state> intron(unsigned n, tactic_state const & s, bool use_unused_names) {
    buffer<name> tmp;
    return intron(n, s, tmp, use_unused_names);
}

vm_obj tactic_intron(vm_obj const & num, vm_obj const & s) {
    optional<metavar_decl> g = tactic::to_state(s).get_main_goal_decl();
    if (!g) return mk_no_goals_exception(tactic::to_state(s));
    buffer<name> new_Hs;
    bool use_unused_names = true;
    if (auto new_s = intron(force_to_unsigned(num, 0), tactic::to_state(s), new_Hs, use_unused_names))
        return tactic::mk_success(*new_s);
    else
        return tactic::mk_exception("intron tactic failed, insufficient binders", tactic::to_state(s));
}

vm_obj intro(name const & n, tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context_old ctx     = mk_type_context_for(s);
    expr type            = g->get_type();
    if (!is_pi(type) && !is_let(type)) {
        type             = ctx.whnf(type);
        if (!is_pi(type))
            return tactic::mk_exception("intro tactic failed, Pi/let expression expected", s);
    }
    local_context lctx   = g->get_context();
    if (is_pi(type)) {
        name n1              = n == "_" ? lctx.get_unused_name(binding_name(type)) : n;
        expr H               = lctx.mk_local_decl(n1, annotated_head_beta_reduce(binding_domain(type)), binding_info(type));
        expr new_type        = instantiate(binding_body(type), H);
        expr new_M           = ctx.mk_metavar_decl(lctx, new_type);
        expr new_val         = mk_lambda(n1, binding_domain(type), mk_delayed_abstraction(new_M, mlocal_name(H)));
        metavar_context mctx = ctx.mctx();
        mctx.assign(head(s.goals()), new_val);
        list<expr> new_gs(new_M, tail(s.goals()));
        return tactic::mk_success(to_obj(H), set_mctx_goals(s, mctx, new_gs));
    } else {
        lean_assert(is_let(type));
        name n1              = n == "_" ? lctx.get_unused_name(let_name(type)) : n;
        expr H               = lctx.mk_local_decl(n1, annotated_head_beta_reduce(let_type(type)), let_value(type));
        expr new_type        = instantiate(let_body(type), H);
        expr new_M           = ctx.mk_metavar_decl(lctx, new_type);
        expr new_val         = mk_let(n1, let_type(type), let_value(type), mk_delayed_abstraction(new_M, mlocal_name(H)));
        ctx.assign(head(s.goals()), new_val);
        list<expr> new_gs(new_M, tail(s.goals()));
        return tactic::mk_success(to_obj(H), set_mctx_goals(s, ctx.mctx(), new_gs));
    }
}

vm_obj tactic_intro(vm_obj const & n, vm_obj const & s) {
    return intro(to_name(n), tactic::to_state(s));
}

void initialize_intro_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "intro_core"}), tactic_intro);
    DECLARE_VM_BUILTIN(name({"tactic", "intron"}),     tactic_intron);
}

void finalize_intro_tactic() {
}
}

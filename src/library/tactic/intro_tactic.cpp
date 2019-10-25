/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/util.h"
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
            new_Hns.push_back(local_name(H));

        } else {
            lean_assert(is_let(type));
            name H_name = mk_name(ctx.lctx(), let_name(type));
            expr H      = new_locals.push_let(H_name, annotated_head_beta_reduce(let_type(type)), let_value(type));
            type        = instantiate(let_body(type), H);
            new_Hs.push_back(H);
            new_Hns.push_back(local_name(H));
        }
    }
    expr new_M   = ctx.mk_metavar_decl(ctx.lctx(), type);
    mctx = ctx.mctx();
    mctx.assign_delayed(mvar, ctx.lctx(), exprs(new_Hs), new_M);
    return some_expr(new_M);
}

static name mk_aux_name(local_context const & lctx, names & given_names, name const & default_name,
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
                      expr const & mvar, unsigned n, names & given_names, buffer<name> & new_Hns,
                      bool use_unused_names) {
    return intron_core(env, opts, mctx, mvar, n, new_Hns,
                       [&](local_context const & lctx, name const & n) {
                           return mk_aux_name(lctx, given_names, n, use_unused_names);
                       });
}

optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, names & given_names, bool use_unused_names) {
    buffer<name> tmp;
    return intron(env, opts, mctx, mvar, n, given_names, tmp, use_unused_names);
}

optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, bool use_unused_names) {
    names empty;
    return intron(env, opts, mctx, mvar, n, empty, use_unused_names);
}

optional<expr> intron(environment const & env, options const & opts, metavar_context & mctx,
                      expr const & mvar, unsigned n, buffer<name> & new_Hns, bool use_unused_names) {
    names empty;
    return intron(env, opts, mctx, mvar, n, empty, new_Hns, use_unused_names);
}

optional<tactic_state> intron(unsigned n, tactic_state const & s, buffer<name> & new_Hns, bool use_unused_names) {
    if (n == 0) return some_tactic_state(s);
    optional<expr> mvar  = s.get_main_goal();
    if (!mvar) return none_tactic_state();
    names new_names;
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

void initialize_intro_tactic() {
}

void finalize_intro_tactic() {
}
}

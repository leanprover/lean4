/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/user_recursors.h"
#include "library/locals.h"
#include "library/app_builder.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_list.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/revert_tactic.h"
#include "library/tactic/intro_tactic.h"

namespace lean {
static vm_obj mk_ill_formed_recursor_exception(recursor_info const & rec_info, tactic_state const & s) {
    return mk_tactic_exception(sstream() << "invalid 'induction' tactic, recursor '" << rec_info.get_name()
                               << "' is ill-formed", s);
}

struct set_intron_failed {};

static void set_intron(expr & R, type_context & ctx, expr const & M, unsigned n, list<name> & ns) {
    if (n == 0) {
        R = M;
    } else {
        metavar_context mctx = ctx.mctx();
        if (auto M1 = intron(ctx.env(), ctx.get_options(), mctx, M, n, ns)) {
            R = *M1;
            ctx.set_mctx(mctx);
        } else {
            throw set_intron_failed();
        }
    }
}

static void set_intron(expr & R, type_context & ctx, expr const & M, unsigned n) {
    list<name> tmp;
    set_intron(R, ctx, M, n, tmp);
}

/* Helper function for computing the number of nested Pi-expressions.
   It uses head_beta_reduce on intermediate terms. */
static unsigned get_expr_arity(expr type) {
    unsigned r = 0;
    type = head_beta_reduce(type);
    while (is_pi(type)) {
        type = head_beta_reduce(binding_body(type));
        r++;
    }
    return r;
}

static vm_obj apply_induction_tactic(tactic_state const & s0, tactic_state const & s,
                                     transparency_mode m, unsigned num_indices, unsigned total_reverted,
                                     list<name> ns, recursor_info const & rec_info) {
    lean_assert(total_reverted >= num_indices+1);
    buffer<name> indices_H;
    optional<tactic_state> s1 = intron(num_indices+1, s, indices_H);
    if (!s1)
        return mk_tactic_exception("invalid 'induction' tactic, failed to reintroduce major premise", s0);
    type_context ctx   = mk_type_context_for(*s1, m);
    metavar_decl g     = *s1->get_main_goal_decl();
    local_context lctx = g.get_context();
    buffer<expr> indices;
    for (unsigned i = 0; i < indices_H.size() - 1; i++)
        indices.push_back(lctx.get_local_decl(indices_H[i])->mk_ref());
    level g_lvl        = get_level(ctx, g.get_type());
    local_decl H_decl  = *lctx.get_last_local_decl();
    expr H             = H_decl.mk_ref();
    expr H_type        = H_decl.get_type();
    buffer<expr> H_type_args;
    expr const & I     = get_app_args(H_type, H_type_args);
    if (!is_constant(I))
        return mk_tactic_exception("invalid 'induction' tactic, major premise is not of the form (C ...)", s0);
    /* Compute recursor universe levels */
    buffer<level> I_lvls;
    to_buffer(const_levels(I), I_lvls);
    bool found_g_lvl = false;
    buffer<level> rec_lvls;
    for (unsigned idx : rec_info.get_universe_pos()) {
        if (idx == recursor_info::get_motive_univ_idx()) {
            rec_lvls.push_back(g_lvl);
            found_g_lvl = true;
        } else {
            if (idx >= I_lvls.size())
                return mk_ill_formed_recursor_exception(rec_info, s0);
            rec_lvls.push_back(I_lvls[idx]);
        }
    }
    if (!found_g_lvl && !is_zero(g_lvl)) {
        return mk_tactic_exception(sstream() << "invalid 'induction' tactic, recursor '" << rec_info.get_name()
                                   << "' can only eliminate into Prop", s0);
    }
    expr rec = mk_constant(rec_info.get_name(), to_list(rec_lvls));
    /* Compute recursor parameters */
    unsigned nparams = 0;
    for (optional<unsigned> const & pos : rec_info.get_params_pos()) {
        if (pos) {
            /* See test at induction_tactic_core */
            lean_assert(*pos < H_type_args.size());
            rec = mk_app(rec, H_type_args[*pos]);
        } else {
            expr rec_type = ctx.relaxed_whnf(ctx.infer(rec));
            if (!is_pi(rec_type))
                return mk_ill_formed_recursor_exception(rec_info, s0);
            optional<expr> inst = ctx.mk_class_instance(binding_domain(rec_type));
            if (!inst)
                return mk_tactic_exception(sstream() << "invalid 'induction' tactic, failed to generate "
                                           "type class instance parameter", s0);
            rec = mk_app(rec, *inst);
        }
        nparams++;
    }
    /* Save initial arity */
    unsigned initial_arity = get_expr_arity(g.get_type());
    /* Compute motive */
    expr motive = g.get_type();
    if (rec_info.has_dep_elim())
        motive  = ctx.mk_lambda(H, motive);
    motive = ctx.mk_lambda(indices, motive);
    rec      = mk_app(rec, motive);
    /* Process remaining arguments and create new goals */
    unsigned curr_pos      = nparams + 1 /* motive */;
    expr rec_type          = ctx.relaxed_try_to_pi(ctx.infer(rec));
    unsigned first_idx_pos = rec_info.get_first_index_pos();
    bool consumed_major    = false;
    buffer<expr> new_goals;
    list<bool> produce_motive = rec_info.get_produce_motive();
    while (is_pi(rec_type) && curr_pos < rec_info.get_num_args()) {
        if (first_idx_pos == curr_pos) {
            for (expr const & idx : indices) {
                rec      = mk_app(rec, idx);
                rec_type = ctx.relaxed_whnf(instantiate(binding_body(rec_type), idx));
                if (!is_pi(rec_type)) {
                    return mk_ill_formed_recursor_exception(rec_info, s0);
                }
                curr_pos++;
            }
            rec      = mk_app(rec, H);
            rec_type = ctx.relaxed_try_to_pi(instantiate(binding_body(rec_type), H));
            consumed_major = true;
            curr_pos++;
        } else {
            if (!produce_motive)
                return mk_ill_formed_recursor_exception(rec_info, s0);
            expr new_type  = head_beta_reduce(binding_domain(rec_type));
            expr rec_arg;
            if (binding_info(rec_type).is_inst_implicit()) {
                if (optional<expr> inst = ctx.mk_class_instance(new_type)) {
                    rec_arg = *inst;
                } else {
                    /* Add new goal if type class inference failed */
                    expr new_goal = ctx.mk_metavar_decl(lctx, new_type);
                    new_goals.push_back(new_goal);
                    rec_arg = new_goal;
                }
            } else {
                unsigned arity = get_expr_arity(new_type);
                lean_assert(arity >= initial_arity);
                lean_assert(total_reverted >= num_indices + 1);
                unsigned nparams = arity - initial_arity; /* number of hypotheses due to minor premise */
                unsigned nextra  = total_reverted - num_indices - 1; /* extra dependencies that have been reverted */
                expr new_M       = ctx.mk_metavar_decl(ctx.lctx(), head_beta_reduce(new_type));
                expr aux_M;
                try {
                    set_intron(aux_M, ctx, new_M, nparams, ns);
                    set_intron(aux_M, ctx, aux_M, nextra);
                } catch (set_intron_failed &) {
                    return mk_tactic_exception("invalid 'induction' tactic, failed to create new goal", s0);
                }
                new_goals.push_back(aux_M);
                rec_arg = new_M;
            }
            produce_motive = tail(produce_motive);
            rec            = mk_app(rec, rec_arg);
            rec_type       = ctx.relaxed_try_to_pi(instantiate(binding_body(rec_type), rec_arg));
            curr_pos++;
        }
    }
    if (!consumed_major) {
        return mk_ill_formed_recursor_exception(rec_info, s0);
    }
    metavar_context mctx = ctx.mctx();
    mctx.assign(head(s1->goals()), rec);
    list<expr> new_gs = to_list(new_goals.begin(), new_goals.end(), tail(s1->goals()));
    tactic_state s2   = set_mctx_goals(*s1, mctx, new_gs);
    return mk_tactic_success(s2);
}

vm_obj induction_tactic_core(transparency_mode const & m, expr const & H, name const & rec, list<name> const & ns,
                             tactic_state const & s) {
    optional<metavar_decl> g = s.get_main_goal_decl();
    if (!g) return mk_no_goals_exception(s);
    type_context ctx = mk_type_context_for(s, m);
    environment const & env = ctx.env();
    if (!is_local(H)) return mk_tactic_exception("invalid 'induction' tactic, argument is not a hypothesis", s);
    expr H_type = ctx.infer(H);
    try {
        recursor_info rec_info = get_recursor_info(env, rec);
        buffer<expr> H_type_args;
        get_app_args(H_type, H_type_args);
        for (optional<unsigned> const & pos : rec_info.get_params_pos()) {
            if (*pos >= H_type_args.size()) {
                return mk_tactic_exception("invalid 'induction' tactic, major premise type is ill-formed", s);
            }
        }
        buffer<expr> indices;
        list<unsigned> const & idx_pos = rec_info.get_indices_pos();
        for (unsigned pos : idx_pos) {
            if (pos >= H_type_args.size()) {
                return mk_tactic_exception("invalid 'induction' tactic, major premise type is ill-formed", s);
            }
            expr const & idx = H_type_args[pos];
            if (!is_local(idx)) {
                return mk_tactic_exception(sstream() << "invalid 'induction' tactic, argument #"
                                        << pos+1 << " of major premise '" << H << "' type is not a variable", s);
            }
            for (unsigned i = 0; i < H_type_args.size(); i++) {
                if (i != pos && is_local(H_type_args[i]) && mlocal_name(H_type_args[i]) == mlocal_name(idx)) {
                    return mk_tactic_exception(sstream() << "invalid 'induction' tactic, argument #"
                                            << pos+1 << " of major premise '" << H << "' type is an index, "
                                            << "but it occurs more than once", s);
                }
                if (i < pos && depends_on(H_type_args[i], idx)) {
                    return mk_tactic_exception(sstream() << "invalid 'induction' tactic, argument #"
                                            << pos+1 << " of major premise '" << H << "' type is an index, "
                                            << "but it occurs in previous arguments", s);
                }
                if (i > pos && // occurs after idx
                    std::find(idx_pos.begin(), idx_pos.end(), i) != idx_pos.end() && // it is also an index
                    is_local(H_type_args[i]) && // if it is not an index, it will fail anyway.
                    depends_on(mlocal_type(idx), H_type_args[i])) {
                    return mk_tactic_exception(sstream() << "invalid 'induction' tactic, argument #"
                                            << pos+1 << " of major premise '" << H << "' type is an index, "
                                            << "but its type depends on the index at position #" << i+1, s);
                }
            }
            indices.push_back(idx);
        }
        if (!rec_info.has_dep_elim() && depends_on(g->get_type(), H)) {
            return mk_tactic_exception(sstream() << "invalid 'induction' tactic, recursor '" << rec
                                    << "' does not support dependent elimination, but conclusion "
                                    << "depends on major premise '" << H << "'", s);
        }
        buffer<expr> to_revert;
        to_revert.append(indices);
        to_revert.push_back(H);
        tactic_state s1 = revert(to_revert, s);
        return apply_induction_tactic(s, s1, m, indices.size(), to_revert.size(), ns, rec_info);
    } catch (exception const & ex) {
        return mk_tactic_exception(sstream() << "invalid 'induction' tactic, " << ex.what(), s);
    }
}

vm_obj tactic_induction_core(vm_obj const & m, vm_obj const & H, vm_obj const & rec, vm_obj const & ns, vm_obj const & s) {
    return induction_tactic_core(to_transparency_mode(m), to_expr(H), to_name(rec), to_list_name(ns), to_tactic_state(s));
}

void initialize_induction_tactic() {
    DECLARE_VM_BUILTIN(name({"tactic", "induction_core"}), tactic_induction_core);
}

void finalize_induction_tactic() {
}
}

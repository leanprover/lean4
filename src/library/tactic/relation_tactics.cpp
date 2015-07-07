/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/relation_manager.h"
#include "library/explicit.h"
#include "library/placeholder.h"
#include "library/tactic/apply_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
// Remark: if no_meta == true, then return none if goal contains metavariables
static optional<name> get_goal_op(proof_state const & s, bool no_meta = false) {
    goals const & gs = s.get_goals();
    if (empty(gs)) {
        throw_no_goal_if_enabled(s);
        return optional<name>();
    }
    goal const & g   = head(gs);
    if (no_meta && has_metavar(g.get_type()))
        return optional<name>();
    expr op  = get_app_fn(head_beta_reduce(g.get_type()));
    if (is_constant(op))
        return optional<name>(const_name(op));
    else
        return optional<name>();
}

tactic refl_tactic(elaborate_fn const & elab, bool no_meta = false) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        auto op = get_goal_op(s, no_meta);
        if (!op)
            return proof_state_seq();
        if (auto refl = get_refl_info(env, *op)) {
            return apply_tactic(elab, mk_constant(*refl))(env, ios, s);
        } else {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'reflexivity' tactic, operator '" << *op << "' is not marked are reflexive");
            return proof_state_seq();
        }
    };
    return tactic(fn);
}

tactic symm_tactic(elaborate_fn const & elab) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        auto op = get_goal_op(s);
        if (!op)
            return proof_state_seq();
        if (auto symm = get_symm_info(env, *op)) {
            return apply_tactic(elab, mk_constant(*symm))(env, ios, s);
        } else {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'symmetry' tactic, operator '" << *op << "' is not marked are symmetric");
            return proof_state_seq();
        }
    };
    return tactic(fn);
}

tactic trans_tactic(elaborate_fn const & elab, expr const & e) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        auto op = get_goal_op(s);
        if (!op)
            return proof_state_seq();
        if (auto info = get_trans_extra_info(env, *op, *op)) {
            expr pr = mk_explicit(mk_constant(info->m_name));
            unsigned nargs = info->m_num_args;
            lean_assert(nargs >= 5);
            for (unsigned i = 0; i < nargs - 4; i++)
                pr = mk_app(pr, mk_expr_placeholder());
            pr = mk_app(pr, e);
            return apply_tactic(elab, pr)(env, ios, s);
        } else {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'transitivity' tactic, operator '" << *op << "' is not marked are transitive");
            return proof_state_seq();
        }
    };
    return tactic(fn);
}

void initialize_relation_tactics() {
    register_tac(name{"tactic", "reflexivity"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return refl_tactic(fn);
                 });
    register_tac(name{"tactic", "symmetry"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return symm_tactic(fn);
                 });
    register_tac(name{"tactic", "transitivity"},
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'transitivity' tactic, invalid argument");
                     return trans_tactic(fn, get_tactic_expr_expr(app_arg(e)));
                 });
}
void finalize_relation_tactics() {}
}

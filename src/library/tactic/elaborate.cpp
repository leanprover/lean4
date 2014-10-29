/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/reducible.h"
#include "library/unifier.h"
#include "library/tactic/elaborate.h"

namespace lean {
bool solve_constraints(environment const & env, io_state const & ios, proof_state & ps, constraint_seq const & cs) {
    if (!cs)
        return true;
    unifier_config cfg(ios.get_options());
    buffer<constraint> cs_buffer;
    cs.linearize(cs_buffer);
    to_buffer(ps.get_postponed(), cs_buffer);
    name_generator ngen   = ps.get_ngen();
    substitution subst    = ps.get_subst();
    unify_result_seq rseq = unify(env, cs_buffer.size(), cs_buffer.data(), ngen.mk_child(), subst, cfg);
    if (auto p = rseq.pull()) {
        substitution new_subst     = p->first.first;
        constraints  new_postponed = p->first.second;
        ps = proof_state(ps.get_goals(), new_subst, ngen, new_postponed);
        return true;
    } else {
        return false;
    }
}

optional<expr> elaborate_with_respect_to(environment const & env, io_state const & ios, elaborate_fn const & elab,
                                         proof_state & s, expr const & e, optional<expr> const & expected_type) {
    name_generator ngen = s.get_ngen();
    substitution subst  = s.get_subst();
    goals const & gs    = s.get_goals();
    if (empty(gs))
        return none_expr();
    auto ecs = elab(head(gs), ngen.mk_child(), e);
    expr new_e = ecs.first;
    buffer<constraint> cs;
    to_buffer(ecs.second, cs);
    if (cs.empty() && !expected_type) {
        // easy case: no constraints to be solved
        s = proof_state(s, ngen);
        return some_expr(new_e);
    } else {
        to_buffer(s.get_postponed(), cs);
        if (expected_type) {
            auto tc      = mk_type_checker(env, ngen.mk_child());
            auto e_t_cs  = tc->infer(new_e);
            expr t       = subst.instantiate(*expected_type);
            e_t_cs.second.linearize(cs);
            auto d_cs    = tc->is_def_eq(e_t_cs.first, t);
            if (!d_cs.first)
                return none_expr();
            d_cs.second.linearize(cs);
        }
        unifier_config cfg(ios.get_options());
        unify_result_seq rseq = unify(env, cs.size(), cs.data(), ngen.mk_child(), subst, cfg);
        if (auto p = rseq.pull()) {
            substitution new_subst     = p->first.first;
            constraints  new_postponed = p->first.second;
            new_e = new_subst.instantiate(new_e);
            s = proof_state(gs, new_subst, ngen, new_postponed);
            return some_expr(new_e);
        } else {
            return none_expr();
        }
    }
}
}

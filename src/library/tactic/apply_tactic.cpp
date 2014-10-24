/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/reducible.h"
#include "library/kernel_bindings.h"
#include "library/unifier.h"
#include "library/occurs.h"
#include "library/metavar_closure.h"
#include "library/type_util.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
/**
    \brief Given a sequence metas: <tt>(?m_1 ...) (?m_2 ... ) ... (?m_k ...)</tt>,
    we say ?m_i is "redundant" if it occurs in the type of some ?m_j.
    This procedure removes from metas any redundant element.
*/
static void remove_redundant_metas(buffer<expr> & metas) {
    buffer<expr> mvars;
    for (expr const & m : metas)
        mvars.push_back(get_app_fn(m));
    unsigned k = 0;
    for (unsigned i = 0; i < metas.size(); i++) {
        bool found = false;
        for (unsigned j = 0; j < metas.size(); j++) {
            if (j != i) {
                if (occurs(mvars[i], mlocal_type(mvars[j]))) {
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

enum subgoals_action_kind { IgnoreSubgoals, AddRevSubgoals, AddSubgoals };

static proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s,
                                         expr const & _e, buffer<constraint> & cs,
                                         bool add_meta, subgoals_action_kind subgoals_action, bool relax_main_opaque) {
    goals const & gs = s.get_goals();
    if (empty(gs))
        return proof_state_seq();
    name_generator ngen = s.get_ngen();
    std::shared_ptr<type_checker> tc(mk_type_checker(env, ngen.mk_child(), relax_main_opaque));
    goal  g          = head(gs);
    goals tail_gs    = tail(gs);
    expr  t          = g.get_type();
    expr  e          = _e;
    auto e_t_cs      = tc->infer(e);
    e_t_cs.second.linearize(cs);
    expr  e_t        = e_t_cs.first;
    buffer<expr> metas;
    if (add_meta) {
        // unsigned num_t   = get_expect_num_args(*tc, t);
        unsigned num_e_t = get_expect_num_args(*tc, e_t);
        // Remark: we used to add (num_e_t - num_t) arguments.
        // This would allow us to handle (A -> B) without using intros,
        // but it was preventing us from solving other problems
        for (unsigned i = 0; i < num_e_t; i++) {
            auto e_t_cs = tc->whnf(e_t);
            e_t_cs.second.linearize(cs);
            e_t        = e_t_cs.first;
            expr meta  = g.mk_meta(ngen.next(), binding_domain(e_t));
            e          = mk_app(e, meta);
            e_t        = instantiate(binding_body(e_t), meta);
            metas.push_back(meta);
        }
    }
    metavar_closure cls(t);
    cls.mk_constraints(s.get_subst(), justification(), relax_main_opaque);
    pair<bool, constraint_seq> dcs = tc->is_def_eq(t, e_t);
    if (!dcs.first)
        return proof_state_seq();
    dcs.second.linearize(cs);
    unifier_config cfg(ios.get_options());
    unify_result_seq rseq = unify(env, cs.size(), cs.data(), ngen.mk_child(), s.get_subst(), cfg);
    list<expr> meta_lst   = to_list(metas.begin(), metas.end());
    return map2<proof_state>(rseq, [=](pair<substitution, constraints> const & p) -> proof_state {
            substitution const & subst    = p.first;
            constraints const & postponed = p.second;
            name_generator new_ngen(ngen);
            substitution new_subst = subst;
            expr new_e = new_subst.instantiate_all(e);
            expr new_p = g.abstract(new_e);
            check_has_no_local(new_p, _e, "apply");
            new_subst.assign(g.get_name(), new_p);
            goals new_gs = tail_gs;
            if (subgoals_action != IgnoreSubgoals) {
                buffer<expr> metas;
                for (auto m : meta_lst) {
                    if (!new_subst.is_assigned(get_app_fn(m)))
                        metas.push_back(m);
                }
                if (subgoals_action == AddRevSubgoals) {
                    for (unsigned i = 0; i < metas.size(); i++)
                        new_gs = cons(goal(metas[i], new_subst.instantiate_all(tc->infer(metas[i]).first)), new_gs);
                } else {
                    lean_assert(subgoals_action == AddSubgoals);
                    remove_redundant_metas(metas);
                    unsigned i = metas.size();
                    while (i > 0) {
                        --i;
                        new_gs = cons(goal(metas[i], new_subst.instantiate_all(tc->infer(metas[i]).first)), new_gs);
                    }
                }
            }
            return proof_state(new_gs, new_subst, new_ngen, postponed);
        });
}

static proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s, expr const & e,
                                         bool add_meta, subgoals_action_kind subgoals_action, bool relax_main_opaque) {
    buffer<constraint> cs;
    return apply_tactic_core(env, ios, s, e, cs, add_meta, subgoals_action, relax_main_opaque);
}

tactic eassumption_tactic(bool relax_main_opaque) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs))
                return proof_state_seq();
            proof_state_seq r;
            goal g = head(gs);
            buffer<expr> hs;
            get_app_args(g.get_meta(), hs);
            for (expr const & h : hs) {
                r = append(r, apply_tactic_core(env, ios, s, h, false, IgnoreSubgoals, relax_main_opaque));
            }
            return r;
        });
}

tactic apply_tactic(elaborate_fn const & elab, expr const & e, bool rev, bool relax_main_opaque) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs))
                return proof_state_seq();
            goal const & g      = head(gs);
            name_generator ngen = s.get_ngen();
            expr       new_e;
            buffer<constraint> cs;
            auto ecs = elab(g, ngen.mk_child(), e);
            new_e    = ecs.first;
            to_buffer(ecs.second, cs);
            to_buffer(s.get_postponed(), cs);
            proof_state new_s(s.get_goals(), s.get_subst(), ngen, constraints());
            return apply_tactic_core(env, ios, new_s, new_e, cs, true, rev ? AddRevSubgoals : AddSubgoals, relax_main_opaque);
        });
}

int mk_eassumption_tactic(lua_State * L) { return push_tactic(L, eassumption_tactic()); }
void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_eassumption_tactic, "eassumption_tac");
}

void initialize_apply_tactic() {
    register_tac(name({"tactic", "apply"}),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'apply' tactic, invalid argument");
                     return apply_tactic(fn, get_tactic_expr_expr(app_arg(e)), false);
                 });

    register_tac(name({"tactic", "rapply"}),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'apply' tactic, invalid argument");
                     return apply_tactic(fn, get_tactic_expr_expr(app_arg(e)), true);
                 });

    register_simple_tac(name({"tactic", "eassumption"}),
                        []() { return eassumption_tactic(); });
}

void finalize_apply_tactic() {
}
}

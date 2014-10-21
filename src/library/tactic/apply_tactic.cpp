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
#include "library/tactic/apply_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
static proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s,
                                         expr const & _e, buffer<constraint> & cs,
                                         bool add_meta, bool add_subgoals, bool relax_main_opaque) {
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
        unsigned num_t   = get_expect_num_args(*tc, t);
        unsigned num_e_t = get_expect_num_args(*tc, e_t);
        if (num_t > num_e_t)
            return proof_state_seq(); // no hope to unify then
        for (unsigned i = 0; i < num_e_t - num_t; i++) {
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
            if (add_subgoals) {
                buffer<expr> metas;
                for (auto m : meta_lst) {
                    if (!new_subst.is_assigned(get_app_fn(m)))
                        metas.push_back(m);
                }
                for (unsigned i = 0; i < metas.size(); i++)
                    new_gs = cons(goal(metas[i], new_subst.instantiate_all(tc->infer(metas[i]).first)), new_gs);
            }
            return proof_state(new_gs, new_subst, new_ngen, postponed);
        });
}

static proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s, expr const & e,
                                         bool add_meta, bool add_subgoals, bool relax_main_opaque) {
    buffer<constraint> cs;
    return apply_tactic_core(env, ios, s, e, cs, add_meta, add_subgoals, relax_main_opaque);
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
                r = append(r, apply_tactic_core(env, ios, s, h, false, false, relax_main_opaque));
            }
            return r;
        });
}

tactic apply_tactic(elaborate_fn const & elab, expr const & e, bool relax_main_opaque) {
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
            return apply_tactic_core(env, ios, new_s, new_e, cs, true, true, relax_main_opaque);
        });
}

int mk_eassumption_tactic(lua_State * L) { return push_tactic(L, eassumption_tactic()); }
void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_eassumption_tactic, "eassumption_tac");
}

static name * g_apply_tactic_name = nullptr;

expr mk_apply_tactic_macro(expr const & e) {
    return mk_tactic_macro(*g_apply_tactic_name, e);
}

void initialize_apply_tactic() {
    g_apply_tactic_name = new name({"tactic", "apply"});
    auto fn = [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
        check_macro_args(e, 1, "invalid 'apply' tactic, it must have one argument");
        return apply_tactic(fn, macro_arg(e, 0));
    };
    register_tactic_macro(*g_apply_tactic_name, fn);

    register_simple_tac(name({"tactic", "eassumption"}),
                        []() { return eassumption_tactic(); });
}

void finalize_apply_tactic() {
    delete g_apply_tactic_name;
}
}

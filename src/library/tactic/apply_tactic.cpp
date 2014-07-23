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
#include "library/kernel_bindings.h"
#include "library/unifier.h"
#include "library/occurs.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
/**
   \brief Traverse \c e and collect metavariable applications (?m l1 ... ln), and store in result.
   The function only succeeds if all metavariable applications are "simple", i.e., the arguments
   are distinct local constants.
*/
bool collect_simple_metas(expr const & e, buffer<expr> & result) {
    bool failed = false;
    // collect metavariables
    for_each(e, [&](expr const & e, unsigned) {
            if (is_meta(e)) {
                if (!is_simple_meta(e)) {
                    failed = true;
                } else {
                    result.push_back(e);
                    return false; /* do not visit type */
                }
            }
            return !failed && has_metavar(e);
        });
    return !failed;
}

unsigned get_expect_num_args(type_checker & tc, expr e) {
    unsigned r = 0;
    while (true) {
        e = tc.whnf(e);
        if (!is_pi(e))
            return r;
        e = binding_body(e);
        r++;
    }
}

void collect_simple_meta(expr const & e, buffer<expr> & metas) {
    for_each(e, [&](expr const & e, unsigned) {
            if (is_meta(e)) {
                if (is_simple_meta(e))
                    metas.push_back(e);
                return false; /* do not visit its type */
            }
            return has_metavar(e);
        });
}

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

proof_state_seq apply_tactic_core(environment const & env, io_state const & ios, proof_state const & s, expr const & _e,
                                  bool add_meta, bool add_subgoals) {
    goals const & gs = s.get_goals();
    if (empty(gs))
        return proof_state_seq();
    name_generator ngen = s.get_ngen();
    type_checker tc(env, ngen.mk_child());
    goal  g          = head(gs);
    goals tail_gs    = tail(gs);
    expr  t          = g.get_type();
    expr  e          = _e;
    expr  e_t        = tc.infer(e);
    buffer<expr> metas;
    collect_simple_meta(e, metas);
    if (add_meta) {
        unsigned num_t   = get_expect_num_args(tc, t);
        unsigned num_e_t = get_expect_num_args(tc, e_t);
        if (num_t > num_e_t)
            return proof_state_seq(); // no hope to unify then
        for (unsigned i = 0; i < num_e_t - num_t; i++) {
            e_t        = tc.whnf(e_t);
            expr meta  = g.mk_meta(ngen.next(), binding_domain(e_t));
            e          = mk_app(e, meta);
            e_t        = instantiate(binding_body(e_t), meta);
            metas.push_back(meta);
        }
    }
    list<expr> meta_lst = to_list(metas.begin(), metas.end());
    lazy_list<substitution> substs = unify(env, t, e_t, ngen.mk_child(), s.get_subst(), ios.get_options());
    return map2<proof_state>(substs, [=](substitution const & subst) -> proof_state {
            name_generator new_ngen(ngen);
            type_checker tc(env, new_ngen.mk_child());
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
                remove_redundant_metas(metas);
                unsigned i = metas.size();
                while (i > 0) {
                    --i;
                    new_gs = cons(goal(metas[i], new_subst.instantiate_all(tc.infer(metas[i]))), new_gs);
                }
            }
            return proof_state(new_gs, new_subst, new_ngen);
        });
}


level refresh_univ_metavars(level const & l, name_generator & ngen, name_map<level> & level_map) {
    return replace(l, [&](level const & l) {
            if (!has_meta(l))
                return some_level(l);
            if (is_meta(l)) {
                name id = meta_id(l);
                if (auto it = level_map.find(id))
                    return some_level(*it);
                level r = mk_meta_univ(ngen.next());
                level_map.insert(id, r);
                return some_level(r);
            }
            return none_level();
        });
}

expr refresh_univ_metavars(expr const & e, name_generator & ngen) {
    if (has_univ_metavar(e)) {
        name_map<level> level_map;
        return replace(e, [&](expr const & e) {
                if (!has_univ_metavar(e))
                    return some_expr(e);
                if (is_sort(e))
                    return some_expr(update_sort(e, refresh_univ_metavars(sort_level(e), ngen, level_map)));
                if (is_constant(e))
                    return some_expr(update_constant(e, map(const_levels(e), [&](level const & l) {
                                    return refresh_univ_metavars(l, ngen, level_map);
                                })));
                return none_expr();
            });
    } else {
        return e;
    }
}

tactic apply_tactic(expr const & e, bool refresh_univ_mvars) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            if (refresh_univ_mvars) {
                name_generator ngen    = s.get_ngen();
                substitution new_subst = s.get_subst();
                expr new_e = refresh_univ_metavars(new_subst.instantiate_all(e), ngen);
                proof_state new_s(s.get_goals(), new_subst, ngen);
                return apply_tactic_core(env, ios, new_s, new_e, true, true);
            } else {
                return apply_tactic_core(env, ios, s, e, true, true);
            }
        });
}

tactic eassumption_tactic() {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs))
                return proof_state_seq();
            proof_state_seq r;
            goal g = head(gs);
            buffer<expr> hs;
            get_app_args(g.get_meta(), hs);
            for (expr const & h : hs) {
                r = append(r, apply_tactic_core(env, ios, s, h, false, false));
            }
            return r;
        });
}

int mk_apply_tactic(lua_State * L) { return push_tactic(L, apply_tactic(to_expr(L, 1))); }
int mk_eassumption_tactic(lua_State * L) { return push_tactic(L, eassumption_tactic()); }
void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_apply_tactic,       "apply_tac");
    SET_GLOBAL_FUN(mk_eassumption_tactic, "eassumption_tac");
}
}

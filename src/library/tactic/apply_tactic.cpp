/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/kernel_bindings.h"
#include "library/unifier.h"
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

tactic apply_tactic(expr const & _e) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
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
            unsigned num_t   = get_expect_num_args(tc, t);
            unsigned num_e_t = get_expect_num_args(tc, e_t);
            if (num_t > num_e_t)
                return proof_state_seq(); // no hope to unify then
            for (unsigned i = 0; i < num_e_t - num_t; i++) {
                e_t        = tc.whnf(e_t);
                expr meta  = g.mk_meta(ngen.next(), binding_domain(e_t));
                e          = mk_app(e, meta);
                e_t        = instantiate(binding_body(e_t), meta);
            }
            lazy_list<substitution> substs = unify(env, t, e_t, ngen.mk_child(), s.get_subst(), ios.get_options());
            return map2<proof_state>(substs, [=](substitution const & subst) -> proof_state {
                    name_generator new_ngen(ngen);
                    type_checker tc(env, new_ngen.mk_child());
                    expr new_e = subst.instantiate(e);
                    expr new_p = g.abstract(new_e);
                    check_has_no_local(new_p, _e, "apply");
                    substitution new_subst = subst.assign(g.get_name(), new_p);
                    buffer<expr> metas;
                    collect_simple_meta(new_e, metas);
                    goals new_gs = tail_gs;
                    unsigned i = metas.size();
                    while (i > 0) {
                        --i;
                        new_gs = cons(goal(metas[i], subst.instantiate(tc.infer(metas[i]))), new_gs);
                    }
                    return proof_state(new_gs, new_subst, new_ngen);
                });
        });
}

int mk_apply_tactic(lua_State * L) { return push_tactic(L, apply_tactic(to_expr(L, 1))); }
void open_apply_tactic(lua_State * L) {
    SET_GLOBAL_FUN(mk_apply_tactic,     "apply_tac");
}
}

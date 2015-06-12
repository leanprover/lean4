/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "kernel/kernel_exception.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/util.h"
#include "library/locals.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/relation_tactics.h"
#include "library/tactic/proof_state.h"

namespace lean {
static void split_deps(buffer<expr> const & hyps, expr const & x, expr const & h,
                       buffer<expr> & non_deps, buffer<expr> & deps, bool & depends_on_h) {
    for (expr const & hyp : hyps) {
        if (hyp == h || hyp == x) {
            // we clear h and x
        } else if (depends_on(hyp, h)) {
            deps.push_back(hyp);
            depends_on_h = true;
        } else if (depends_on(hyp, x) || depends_on_any(hyp, deps)) {
            deps.push_back(hyp);
        } else {
            non_deps.push_back(hyp);
        }
    }
}

optional<proof_state> subst(environment const & env, name const & h_name, bool symm, proof_state const & s) {
    goals const & gs = s.get_goals();
    if (empty(gs))
        return none_proof_state();
    goal g  = head(gs);
    auto opt_h = g.find_hyp_from_internal_name(h_name);
    if (!opt_h)
        return none_proof_state();
    expr const & h = opt_h->first;
    expr lhs, rhs;
    if (!is_eq(mlocal_type(h), lhs, rhs))
        return none_proof_state();
    name_generator ngen = s.get_ngen();
    auto tc = mk_type_checker(env, ngen.mk_child());
    if (symm)
        std::swap(lhs, rhs);
    if (!is_local(lhs))
        return none_proof_state();
    if (depends_on(rhs, lhs)) {
        throw_tactic_exception_if_enabled(s, sstream() << "invalid 'subst' tactic, '" << lhs
                                          << "' occurs in the other side of the equation");
        return none_proof_state();
    }
    buffer<expr> hyps, deps, non_deps;
    g.get_hyps(hyps);
    bool depends_on_h = depends_on(g.get_type(), h);
    split_deps(hyps, lhs, h, non_deps, deps, depends_on_h);
    // revert dependencies
    expr type = Pi(deps, g.get_type());
    // substitute
    bool has_dep_elim = inductive::has_dep_elim(env, get_eq_name());
    bool use_dep_elim = has_dep_elim;
    if (depends_on_h)
        use_dep_elim = true;
    expr motive, new_type;
    new_type = instantiate(abstract_local(type, mlocal_name(lhs)), rhs);
    if (use_dep_elim) {
        new_type = instantiate(abstract_local(new_type, mlocal_name(h)), mk_refl(*tc, rhs));
        if (symm) {
            motive = Fun(lhs, Fun(h, type));
        } else {
            expr Heq = mk_local(ngen.next(), local_pp_name(h), mk_eq(*tc, rhs, lhs), binder_info());
            motive = Fun(lhs, Fun(Heq, type));
        }
    } else {
        motive   = Fun(lhs, type);
    }
    buffer<expr> new_hyps;
    buffer<expr> intros_hyps;
    new_hyps.append(non_deps);

    // reintroduce dependencies
    expr new_goal_type = new_type;
    for (expr const & d : deps) {
        if (!is_pi(new_goal_type))
            return none_proof_state();
        expr new_h = mk_local(ngen.next(), local_pp_name(d), binding_domain(new_goal_type), binder_info());
        new_hyps.push_back(new_h);
        intros_hyps.push_back(new_h);
        new_goal_type = instantiate(binding_body(new_goal_type), new_h);
    }

    // create new goal
    expr new_metavar   = mk_metavar(ngen.next(), Pi(new_hyps, new_goal_type));
    expr new_meta_core = mk_app(new_metavar, non_deps);
    expr new_meta      = mk_app(new_meta_core, intros_hyps);
    goal new_g(new_meta, new_goal_type);
    // create eqrec term
    substitution new_subst = s.get_subst();
    expr major = symm ? h : mk_symm(*tc, h);
    expr minor = new_meta_core;
    expr A     = tc->infer(lhs).first;
    level l1   = sort_level(tc->ensure_type(new_type).first);
    level l2   = sort_level(tc->ensure_type(A).first);
    name eq_rec_name;
    if (!has_dep_elim && use_dep_elim)
        eq_rec_name = get_eq_drec_name();
    else
        eq_rec_name = get_eq_rec_name();
    expr eqrec = mk_app({mk_constant(eq_rec_name, {l1, l2}), A, rhs, motive, minor, lhs, major});
    if (use_dep_elim) {
        try {
            check_term(env, g.abstract(eqrec));
        } catch (kernel_exception & ex) {
            if (!s.report_failure())
                return none_proof_state();
            std::shared_ptr<kernel_exception> saved_ex(static_cast<kernel_exception*>(ex.clone()));
            throw tactic_exception("rewrite step failed", none_expr(), s,
                                   [=](formatter const & fmt) {
                                       format r;
                                       r += format("invalid 'subst' tactic, "
                                                   "produced type incorrect term, details: ");
                                       r += saved_ex->pp(fmt);
                                       r += line();
                                       return r;
                                   });
        }
    }
    expr new_val = mk_app(eqrec, deps);
    assign(new_subst, g, new_val);
    lean_assert(new_subst.is_assigned(g.get_mvar()));
    proof_state new_s(s, goals(new_g, tail(gs)), new_subst, ngen);
    return some_proof_state(new_s);
}

tactic mk_subst_tactic_core(name const & h_name, bool symm) {
    auto fn = [=](environment const & env, io_state const &, proof_state const & s) {
        return subst(env, h_name, symm, s);
    };
    return tactic01(fn);
}

tactic mk_subst_tactic(list<name> const & ids) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        if (!ids)
            return proof_state_seq(s);
        goals const & gs = s.get_goals();
        if (empty(gs))
            return proof_state_seq();
        goal const & g  = head(gs);
        name const & id = head(ids);

        auto apply_rewrite = [&](expr const & H, bool symm) {
            tactic tac = then(mk_subst_tactic_core(mlocal_name(H), symm), mk_subst_tactic(tail(ids)));
            return tac(env, ios, s);
        };

        optional<pair<expr, unsigned>> p = g.find_hyp(id);
        if (!p) {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'subst' tactic, there is no hypothesis named '"
                                              << id << "'");
            return proof_state_seq();
        }
        expr const & H = p->first;
        expr lhs, rhs;
        if (is_eq(mlocal_type(H), lhs, rhs)) {
            if (is_local(rhs)) {
                return apply_rewrite(H, true);
            } else if (is_local(lhs)) {
                return apply_rewrite(H, false);
            } else {
                throw_tactic_exception_if_enabled(s, sstream() << "invalid 'subst' tactic, hypothesis '"
                                                  << id << "' is not of the form (x = t) or (t = x)");
                return proof_state_seq();
            }
        } else if (is_local(H)) {
            expr const & x = H;
            buffer<expr> hyps;
            g.get_hyps(hyps);
            for (expr const & H : hyps) {
                expr lhs, rhs;
                if (is_eq(mlocal_type(H), lhs, rhs)) {
                    if (is_local(lhs) && mlocal_name(lhs) == mlocal_name(x) && !depends_on(rhs, lhs)) {
                        return apply_rewrite(H, false);
                    } else if (is_local(rhs) && mlocal_name(rhs) == mlocal_name(x) && !depends_on(lhs, rhs)) {
                        return apply_rewrite(H, true);
                    }
                }
            }
        }
        throw_tactic_exception_if_enabled(s, sstream() << "invalid 'subst' tactic, hypothesis '"
                                          << id << "' is not a variable nor an equation of the form (x = t) or (t = x)");
        return proof_state_seq();
    };
    return tactic(fn);
}

tactic mk_subst_vars_tactic(bool first, unsigned start) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            if (first)
                return proof_state_seq();
            else
                return proof_state_seq(s);
        }
        goal const & g  = head(gs);

        auto apply_rewrite = [&](expr const & H, bool symm, unsigned i) {
            tactic tac = orelse(then(mk_subst_tactic_core(mlocal_name(H), symm), mk_subst_vars_tactic(false, 0)),
                                mk_subst_vars_tactic(false, i+1));
            return tac(env, ios, s);
        };

        buffer<expr> hyps;
        g.get_hyps(hyps);
        for (unsigned i = start; i < hyps.size(); i++) {
            expr const & h = hyps[i];
            expr lhs, rhs;
            if (is_eq(mlocal_type(h), lhs, rhs)) {
                if (is_local(rhs)) {
                    return apply_rewrite(h, true, i);
                } else if (is_local(lhs)) {
                    return apply_rewrite(h, false, i);
                }
            }
        }
        if (first)
            return proof_state_seq();
        else
            return proof_state_seq(s);
    };
    return tactic(fn);
}

void initialize_subst_tactic() {
    register_tac(name{"tactic", "subst"},
                 [](type_checker &, elaborate_fn const & elab, expr const & e, pos_info_provider const *) {
                     buffer<name> ns;
                     get_tactic_id_list_elements(app_arg(e), ns, "invalid 'subst' tactic, list of identifiers expected");
                     return then(mk_subst_tactic(to_list(ns)), try_tactic(refl_tactic(elab)));
                 });
    register_tac(name{"tactic", "substvars"},
                 [](type_checker &, elaborate_fn const & elab, expr const &, pos_info_provider const *) {
                     return then(mk_subst_vars_tactic(true, 0), try_tactic(refl_tactic(elab)));
                 });
}
void finalize_subst_tactic() {
}
}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
/** \brief Introduce num hypotheses, if _ns is not nil use it to name the hypothesis,

    New hypothesis of the form (a = a) and (a == a) are discarded.
    New hypothesis of the form (a == b) where (a b : A), are converted into (a = b).
*/
tactic intros_num_tactic(list<name> _ns, unsigned num) {
    auto fn = [=](environment const & env, io_state const &, proof_state const & s) {
        if (num == 0)
            return some_proof_state(s);
        list<name> ns    = _ns;
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(s);
            return optional<proof_state>();
        }
        goal const & g      = head(gs);
        name_generator ngen = s.get_ngen();
        auto tc             = mk_type_checker(env, ngen.mk_child(), s.relax_main_opaque());
        expr t              = g.get_type();
        expr m              = g.get_meta();
        buffer<expr> hyps;
        g.get_hyps(hyps);
        buffer<expr> new_hyps; // extra hypotheses for the new goal
        buffer<expr> args;     // arguments to be provided to new goal
        buffer<expr> intros;   // locals being introduced

        auto mk_name = [&](name const & n) {
            if (is_nil(ns)) {
                return get_unused_name(n, new_hyps);
            } else {
                name r = head(ns);
                ns     = tail(ns);
                return r;
            }
        };

        // introduce a value of type t
        auto add_intro = [&](expr const & t) {
            expr i = mk_local(ngen.next(), t);
            intros.push_back(i);
            return i;
        };

        auto add_hyp = [&](name const & n, expr const & t) {
            expr l = mk_local(mk_name(n), t);
            new_hyps.push_back(l);
            intros.push_back(l);
            args.push_back(l);
            return l;
        };

        try {
            for (unsigned i = 0; i < num; i++) {
                t = tc->ensure_pi(t).first;
                name const & Hname = binding_name(t);
                constraint_seq Hcs;
                expr Htype = tc->whnf(binding_domain(t), Hcs);
                optional<expr> new_Htype;
                expr A, B, lhs, rhs;
                if (!closed(binding_body(t))) {
                    // rest depends on Hname : Htype
                    expr H = add_hyp(Hname, Htype);
                    t      = instantiate(binding_body(t), H);
                } else {
                    if (is_eq(Htype, lhs, rhs)) {
                        if (!tc->is_def_eq(lhs, rhs, justification(), Hcs) || Hcs)
                            add_hyp(Hname, Htype);
                        else
                            add_intro(Htype); // discard
                    } else if (is_standard(env) && is_heq(Htype, A, lhs, B, rhs)) {
                        if (tc->is_def_eq(A, B, justification(), Hcs) && !Hcs) {
                            if (!tc->is_def_eq(lhs, rhs, justification(), Hcs) || Hcs) {
                                // convert to homogenous equality
                                expr H         = mk_local(ngen.next(), Htype);
                                expr newHtype  = mk_eq(*tc, lhs, rhs);
                                expr newH      = mk_local(mk_name(Hname), newHtype);
                                new_hyps.push_back(newH);
                                intros.push_back(H);
                                levels heq_lvl = const_levels(get_app_fn(Htype));
                                args.push_back(mk_app(mk_constant(get_heq_to_eq_name(), heq_lvl), A, lhs, rhs, H));
                            } else {
                                add_intro(Htype); // discard
                            }
                        } else {
                            add_hyp(Hname, Htype);
                        }
                    } else {
                        add_hyp(Hname, Htype);
                    }
                    t = binding_body(t);
                }
            }
            substitution new_subst = s.get_subst();
            expr new_mvar = mk_metavar(ngen.next(), Pi(hyps, Pi(new_hyps, t)));
            expr new_aux  = mk_app(new_mvar, hyps);
            expr new_meta = mk_app(new_aux,  new_hyps);
            goal new_goal(new_meta, t);
            assign(new_subst, g, Fun(intros, mk_app(new_aux, args)));
            return some_proof_state(proof_state(s, cons(new_goal, tail(gs)), new_subst, ngen));
        } catch (exception &) {
            return none_proof_state();
        }
    };
    return tactic01(fn);
}

tactic injection_tactic(elaborate_fn const & elab, expr const & e, list<name> const & ids) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        proof_state new_s = s;
        goals const & gs  = new_s.get_goals();
        if (!gs) {
            throw_no_goal_if_enabled(s);
            return proof_state_seq();
        }
        expr t                 = head(gs).get_type();
        bool report_unassigned = true;
        bool enforce_type      = false;
        if (optional<expr> new_e = elaborate_with_respect_to(env, ios, elab, new_s, e, none_expr(),
                                                             report_unassigned, enforce_type)) {
            constraint_seq cs;
            name_generator ngen = new_s.get_ngen();
            auto tc             = mk_type_checker(env, ngen.mk_child(), new_s.relax_main_opaque());
            expr new_e_type     = tc->whnf(tc->infer(*new_e, cs), cs);
            expr lhs, rhs;
            if (!is_eq(new_e_type, lhs, rhs)) {
                throw_tactic_exception_if_enabled(new_s, "invalid 'injection' tactic, "
                                                  "given argument is not an equality proof");
                return proof_state_seq();
            }
            lhs = tc->whnf(lhs, cs);
            rhs = tc->whnf(rhs, cs);
            expr A = tc->whnf(tc->infer(lhs, cs), cs);
            buffer<expr> I_args;
            expr I = get_app_args(A, I_args);
            if (!is_constant(I) || !inductive::is_inductive_decl(env, const_name(I))) {
                throw_tactic_exception_if_enabled(new_s, "invalid 'injection' tactic, "
                                                  "it is not an equality between inductive values");
                return proof_state_seq();
            }
            expr lhs_fn = get_app_fn(lhs);
            expr rhs_fn = get_app_fn(rhs);
            if (!is_constant(lhs_fn) || !is_constant(rhs_fn) || const_name(lhs_fn) != const_name(rhs_fn) ||
                !inductive::is_intro_rule(env, const_name(lhs_fn))) {
                throw_tactic_exception_if_enabled(new_s, "invalid 'injection' tactic, "
                                                  "the given equality is not of the form (f ...) = (f ...) "
                                                  "where f is a constructor");
                return proof_state_seq();
            }
            unsigned num_params  = *inductive::get_num_params(env, const_name(I));
            unsigned cnstr_arity = get_arity(env.get(const_name(lhs_fn)).get_type());
            lean_assert(cnstr_arity >= num_params);
            unsigned num_new_eqs = cnstr_arity - num_params;
            level t_lvl = sort_level(tc->ensure_type(t, cs));
            expr N      = mk_constant(name(const_name(I), "no_confusion"), cons(t_lvl, const_levels(I)));
            N           = mk_app(mk_app(N, I_args), t, lhs, rhs, *new_e);
            if (is_standard(env)) {
                tactic tac = then(apply_tactic_core(N, cs),
                                  intros_num_tactic(ids, num_new_eqs));
                return tac(env, ios, new_s);
            } else {
                level n_lvl    = mk_meta_univ(tc->mk_fresh_name());
                expr lift_down = mk_app(mk_constant(get_lift_down_name(), {t_lvl, n_lvl}), t);
                tactic tac     = then(apply_tactic_core(lift_down),
                                      then(apply_tactic_core(N, cs),
                                           intros_num_tactic(ids, num_new_eqs)));
                return tac(env, ios, new_s);
            }
        } else {
            return proof_state_seq();
        }
    };
    return tactic(fn);
}

void initialize_injection_tactic() {
    register_tac(name{"tactic", "injection"},
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(app_fn(e)), "invalid 'injection' tactic, invalid argument");
                     buffer<name> ids;
                     get_tactic_id_list_elements(app_arg(e), ids, "invalid 'injection' tactic, list of identifiers expected");
                     return injection_tactic(fn, get_tactic_expr_expr(app_arg(app_fn(e))), to_list(ids));
                 });
}

void finalize_injection_tactic() {
}
}

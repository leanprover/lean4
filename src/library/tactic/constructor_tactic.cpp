/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
/**
   \brief Implement multiple variations of the constructor tactic.
   It tries to solve the goal by applying the i-th constructor.
   If \c num_constructors is not none, then the tactic checks wether the inductive datatype has
   the expected number of constructors.
   If \c given_args is provided, then the tactic fixes the given arguments.
   It creates a subgoal for each remaining argument.
*/
tactic constructor_tactic(elaborate_fn const & elab, unsigned _i, optional<unsigned> num_constructors, list<expr> const & given_args) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(s);
            return optional<proof_state>();
        }
        if (_i == 0) {
            throw_tactic_exception_if_enabled(s, "invalid 'constructor' tactic, index must be greater than zero");
            return optional<proof_state>();
        }
        unsigned i = _i - 1;
        name_generator ngen = s.get_ngen();
        auto tc             = mk_type_checker(env, ngen.mk_child(), s.relax_main_opaque());
        goal const & g      = head(gs);
        expr t              = tc->whnf(g.get_type()).first;
        buffer<expr> I_args;
        expr I              = get_app_args(t, I_args);
        if (!is_constant(I) || !inductive::is_inductive_decl(env, const_name(I))) {
            throw_tactic_exception_if_enabled(s, "invalid 'constructor' tactic, goal is not an inductive datatype");
            return none_proof_state();
        }
        buffer<name> c_names;
        get_intro_rule_names(env, const_name(I), c_names);
        if (num_constructors && c_names.size() != *num_constructors) {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'constructor' tactic, goal is an inductive datatype, "
                                              << "but it does not have " << *num_constructors << " constructor(s)");
            return none_proof_state();
        }
        if (i >= c_names.size()) {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'constructor' tactic, goal is an inductive datatype, "
                                              << "but it has only " << c_names.size() << " constructor(s)");
            return none_proof_state();
        }
        expr C              = mk_constant(c_names[i], const_levels(I));
        unsigned num_params = *inductive::get_num_params(env, const_name(I));
        if (I_args.size() < num_params)
            return none_proof_state();
        proof_state new_s(s, ngen);
        C = mk_app(C, num_params, I_args.data());
        expr C_type = tc->whnf(tc->infer(C).first).first;
        bool report_unassigned = true;
        bool enforce_type      = true;
        for (expr const & arg : given_args) {
            if (!is_pi(C_type)) {
                throw_tactic_exception_if_enabled(s, sstream() << "invalid 'constructor' tactic, "
                                                  << "too many arguments have been provided");
                return none_proof_state();
            }
            try {
                if (auto new_arg = elaborate_with_respect_to(env, ios, elab, new_s, arg, some_expr(binding_domain(C_type)),
                                                           report_unassigned, enforce_type)) {
                    C = mk_app(C, *new_arg);
                    C_type = tc->whnf(instantiate(binding_body(C_type), *new_arg)).first;
                } else {
                    return none_proof_state();
                }
            } catch (exception &) {
                if (new_s.report_failure())
                    throw;
                return none_proof_state();
            }
        }
        buffer<goal> new_goals;
        while (is_pi(C_type)) {
            expr new_type = binding_domain(C_type);
            expr new_meta = g.mk_meta(tc->mk_fresh_name(), new_type);
            goal new_goal(new_meta, new_type);
            new_goals.push_back(new_goal);
            C      = mk_app(C, new_meta);
            C_type = tc->whnf(instantiate(binding_body(C_type), new_meta)).first;
        }
        substitution new_subst = new_s.get_subst();
        assign(new_subst, g, C);
        return some_proof_state(proof_state(new_s, to_list(new_goals.begin(), new_goals.end(), tail(gs)), new_subst));
    };
    return tactic01(fn);
}

void initialize_constructor_tactic() {
    register_tac(name{"tactic", "constructor"},
                 [](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     unsigned i = get_unsigned_arg(tc, e, 0);
                     return constructor_tactic(fn, i, optional<unsigned>(), list<expr>());
                 });
    register_tac(name{"tactic", "split"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return constructor_tactic(fn, 1, optional<unsigned>(1), list<expr>());
                 });
    register_tac(name{"tactic", "left"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return constructor_tactic(fn, 1, optional<unsigned>(2), list<expr>());
                 });
    register_tac(name{"tactic", "right"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return constructor_tactic(fn, 2, optional<unsigned>(2), list<expr>());
                 });
    register_tac(name{"tactic", "existsi"},
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'existsi' tactic, invalid argument");
                     expr arg = get_tactic_expr_expr(app_arg(e));
                     return constructor_tactic(fn, 1, optional<unsigned>(1), list<expr>(arg));
                 });
}

void finalize_constructor_tactic() {
}
}

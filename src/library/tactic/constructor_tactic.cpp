/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/lazy_list_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/apply_tactic.h"

namespace lean {
/**
   \brief Implement multiple variations of the constructor tactic.
   It tries to solve the goal by applying the i-th constructor.
   If \c num_constructors is not none, then the tactic checks wether the inductive datatype has
   the expected number of constructors.
   If \c given_args is provided, then the tactic fixes the given arguments.
   It creates a subgoal for each remaining argument.
*/
tactic constructor_tactic(elaborate_fn const & elab, optional<unsigned> _i, optional<unsigned> num_constructors,
                          list<expr> const & given_args, bool use_fapply = false) {
    auto fn = [=](environment const & env, io_state const & ios, proof_state const & s) {
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(s);
            return proof_state_seq();
        }
        constraint_seq cs;
        name_generator ngen = s.get_ngen();
        auto tc             = mk_type_checker(env, ngen.mk_child());
        goal const & g      = head(gs);
        expr t              = tc->whnf(g.get_type(), cs);
        buffer<expr> I_args;
        expr I              = get_app_args(t, I_args);
        if (!is_constant(I) || !inductive::is_inductive_decl(env, const_name(I))) {
            throw_tactic_exception_if_enabled(s, "invalid 'constructor' tactic, goal is not an inductive datatype");
            return proof_state_seq();
        }
        buffer<name> c_names;
        get_intro_rule_names(env, const_name(I), c_names);
        if (num_constructors && c_names.size() != *num_constructors) {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'constructor' tactic, goal is an inductive datatype, "
                                              << "but it does not have " << *num_constructors << " constructor(s)");
            return proof_state_seq();
        }

        auto try_constructor = [&](proof_state const & s, unsigned i) {
            if (i >= c_names.size()) {
                throw_tactic_exception_if_enabled(s, sstream() << "invalid 'constructor' tactic, goal is an inductive datatype, "
                                                  << "but it has only " << c_names.size() << " constructor(s)");
                return proof_state_seq();
            }
            expr C              = mk_constant(c_names[i], const_levels(I));
            unsigned num_params = *inductive::get_num_params(env, const_name(I));
            if (I_args.size() < num_params)
                return proof_state_seq();
            proof_state new_s(s, ngen);
            C = mk_app(C, num_params, I_args.data());
            expr C_type = tc->whnf(tc->infer(C, cs), cs);
            bool report_unassigned = true;
            bool enforce_type      = true;
            for (expr const & arg : given_args) {
                if (!is_pi(C_type)) {
                    throw_tactic_exception_if_enabled(s, sstream() << "invalid 'constructor' tactic, "
                                                      << "too many arguments have been provided");
                    return proof_state_seq();
                }
                try {
                    if (auto new_arg = elaborate_with_respect_to(env, ios, elab, new_s, arg, some_expr(binding_domain(C_type)),
                                                                 report_unassigned, enforce_type)) {
                        C = mk_app(C, *new_arg);
                        C_type = tc->whnf(instantiate(binding_body(C_type), *new_arg), cs);
                    } else {
                        return proof_state_seq();
                    }
                } catch (exception &) {
                    if (new_s.report_failure())
                        throw;
                    return proof_state_seq();
                }
            }
            if (use_fapply)
                return fapply_tactic_core(env, ios, new_s, C, cs);
            else
                return apply_tactic_core(env, ios, new_s, C, cs);
        };

        if (_i) {
            if (*_i == 0) {
                throw_tactic_exception_if_enabled(s, "invalid 'constructor' tactic, index must be greater than zero");
                return proof_state_seq();
            }
            return try_constructor(s, *_i - 1);
        } else {
            proof_state new_s = s.update_report_failure(false);
            proof_state_seq r;
            for (unsigned i = 0; i < c_names.size(); i++)
                r = append(r, try_constructor(new_s, i));
            return r;
        }
    };
    return tactic(fn);
}

void initialize_constructor_tactic() {
    register_tac(name{"tactic", "constructor"},
                 [](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     auto i = get_optional_unsigned(tc, app_arg(e));
                     return constructor_tactic(fn, i, optional<unsigned>(), list<expr>());
                 });
    register_tac(name{"tactic", "fconstructor"},
                 [](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     auto i = get_optional_unsigned(tc, app_arg(e));
                     return constructor_tactic(fn, i, optional<unsigned>(), list<expr>(), true);
                 });
    register_tac(name{"tactic", "split"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return constructor_tactic(fn, optional<unsigned>(1), optional<unsigned>(1), list<expr>());
                 });
    register_tac(name{"tactic", "left"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return constructor_tactic(fn, optional<unsigned>(1), optional<unsigned>(2), list<expr>());
                 });
    register_tac(name{"tactic", "right"},
                 [](type_checker &, elaborate_fn const & fn, expr const &, pos_info_provider const *) {
                     return constructor_tactic(fn, optional<unsigned>(2), optional<unsigned>(2), list<expr>());
                 });
    register_tac(name{"tactic", "existsi"},
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(e), "invalid 'existsi' tactic, invalid argument");
                     expr arg = get_tactic_expr_expr(app_arg(e));
                     return constructor_tactic(fn, optional<unsigned>(1), optional<unsigned>(1), list<expr>(arg));
                 });
}

void finalize_constructor_tactic() {
}
}

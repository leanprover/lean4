/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "kernel/abstract.h"
#include "kernel/kernel_exception.h"
#include "library/reducible.h"
#include "library/util.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
expr mk_generalize_tactic_expr(expr const & e, name const & id) {
    return mk_app(mk_constant(get_tactic_generalize_tac_name()),
                  e, mk_constant(id));
}

tactic generalize_tactic(elaborate_fn const & elab, expr const & e, name const & x) {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & s) {
            proof_state new_s = s;
            if (auto new_e = elaborate_with_respect_to(env, ios, elab, new_s, e)) {
                name_generator ngen = new_s.get_ngen();
                substitution subst  = new_s.get_subst();
                goals const & gs    = new_s.get_goals();
                goal const & g      = head(gs);
                auto tc     = mk_type_checker(env, ngen.mk_child());
                auto e_t_cs = tc->infer(*new_e);
                if (e_t_cs.second) {
                    throw_tactic_exception_if_enabled(s, "invalid 'generalize' tactic, unification constraints "
                                                      "have been generated when inferring type");
                    return none_proof_state(); // constraints were generated
                }
                expr e_t    = e_t_cs.first;
                expr t      = subst.instantiate(g.get_type());
                name n;
                if (is_constant(e))
                    n = const_name(e);
                else if (is_local(e))
                    n = local_pp_name(e);
                else
                    n = x;
                expr new_t = mk_pi(n, e_t, abstract(t, *new_e));
                expr new_m = g.mk_meta(ngen.next(), new_t);
                try {
                    check_term(*tc, g.abstract(new_t));
                } catch (kernel_exception const & ex) {
                    std::shared_ptr<kernel_exception> ex_ptr(static_cast<kernel_exception*>(ex.clone()));
                    throw_tactic_exception_if_enabled(s, [=](formatter const & fmt) {
                            format r = format("invalid 'generalize' tactic, type error");
                            r       += line();
                            r       += ex_ptr->pp(fmt);
                            return r;
                        });
                    return none_proof_state();
                }

                assign(subst, g, mk_app(new_m, *new_e));
                goal new_g(new_m, new_t);
                return some(proof_state(new_s, goals(new_g, tail(gs)), subst, ngen));
            }
            return none_proof_state();
        });
}

void initialize_generalize_tactic() {
    register_tac(get_tactic_generalize_tac_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     check_tactic_expr(app_arg(app_fn(e)), "invalid 'generalize' tactic, invalid argument");
                     name id = tactic_expr_to_id(app_arg(e), "invalid 'generalize' tactic, argument must be an identifier");
                     return generalize_tactic(fn, get_tactic_expr_expr(app_arg(app_fn(e))), id);
                 });

    register_tac(get_tactic_generalizes_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     buffer<expr> args;
                     get_tactic_expr_list_elements(app_arg(e), args, "invalid 'generalizes' tactic, list of expressions expected");
                     if (args.empty())
                         return id_tactic();
                     tactic r = generalize_tactic(fn, args.back(), "x");
                     args.pop_back();
                     while (!args.empty()) {
                         r = then(generalize_tactic(fn, args.back(), "x"), r);
                         args.pop_back();
                     }
                     return r;
                 });
}

void finalize_generalize_tactic() {
}
}

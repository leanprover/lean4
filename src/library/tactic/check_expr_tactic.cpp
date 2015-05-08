/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "library/constants.h"
#include "library/reducible.h"
#include "library/flycheck.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic check_expr_tactic(elaborate_fn const & elab, expr const & e,
                         std::string const & fname, pair<unsigned, unsigned> const & pos) {
    return tactic01([=](environment const & env, io_state const & ios, proof_state const & s) {
            goals const & gs = s.get_goals();
            if (empty(gs)) {
                throw_no_goal_if_enabled(s);
                return none_proof_state();
            }
            goal const & g      = head(gs);
            name_generator ngen = s.get_ngen();
            expr new_e = std::get<0>(elab(g, ngen.mk_child(), e, none_expr(), s.get_subst(), false));
            auto tc = mk_type_checker(env, ngen.mk_child());
            expr new_t = tc->infer(new_e).first;
            auto out = regular(env, ios);
            flycheck_information info(out);
            if (info.enabled()) {
                out << fname << ":" << pos.first << ":" << pos.second << ": information: ";
                out << "check result:\n";
            }
            out << new_e << " : " << new_t << endl;
            return some_proof_state(s);
        });
}

void initialize_check_expr_tactic() {
    register_tac(get_tactic_check_expr_name(),
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
                     check_tactic_expr(app_arg(e), "invalid 'check_expr' tactic, invalid argument");
                     expr arg = get_tactic_expr_expr(app_arg(e));
                     if (p) {
                         if (auto it = p->get_pos_info(e))
                             return check_expr_tactic(fn, arg, std::string(p->get_file_name()), *it);
                     }
                     return check_expr_tactic(fn, arg, "<unknown file>", mk_pair(0, 0));
                 });
}
void finalize_check_expr_tactic() {
}
}

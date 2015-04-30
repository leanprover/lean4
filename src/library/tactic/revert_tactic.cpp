/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/locals.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic revert_tactic(name const & n) {
    auto fn = [=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(s);
            return none_proof_state();
        }
        goal  g          = head(gs);
        goals tail_gs    = tail(gs);
        if (auto p = g.find_hyp(n)) {
            expr const & h = p->first;
            unsigned i     = p->second;
            buffer<expr> hyps;
            g.get_hyps(hyps);
            hyps.erase(hyps.size() - i - 1);
            if (optional<expr> other_h = depends_on(i, hyps.end() - i, h)) {
                throw_tactic_exception_if_enabled(s, sstream() << "invalid 'revert' tactic, hypothesis '" << local_pp_name(*other_h)
                                                  << "' depends on '" << local_pp_name(h) << "'");
                return none_proof_state(); // other hypotheses depend on h
            }
            name_generator ngen = s.get_ngen();
            expr new_type = Pi(h, g.get_type());
            expr new_meta = mk_app(mk_metavar(ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            substitution new_subst = s.get_subst();
            assign(new_subst, g, mk_app(new_meta, h));
            proof_state new_s(s, goals(new_g, tail_gs), new_subst, ngen);
            return some_proof_state(new_s);
        } else {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'revert' tactic, unknown hypothesis '" << n << "'");
            return none_proof_state();
        }
    };
    return tactic01(fn);
}

void initialize_revert_tactic() {
    auto fn = [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
        buffer<name> ns;
        get_tactic_id_list_elements(app_arg(e), ns, "invalid 'reverts' tactic, list of identifiers expected");
        tactic r = revert_tactic(ns[0]);
        for (unsigned i = 1; i < ns.size(); i++)
            r = then(revert_tactic(ns[i]), r);
        return r;
    };
    register_tac(get_tactic_revert_name(), fn);
    register_tac(get_tactic_reverts_name(), fn);
}
void finalize_revert_tactic() {}
}

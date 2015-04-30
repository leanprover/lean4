/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "kernel/abstract.h"
#include "library/locals.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic clear_tactic(name const & n) {
    auto fn = [=](environment const &, io_state const &, proof_state const & _s) -> optional<proof_state> {
        if (!_s.get_goals()) {
            throw_no_goal_if_enabled(_s);
            return none_proof_state();
        }
        proof_state s    = apply_substitution(_s);
        goals const & gs = s.get_goals();
        goal  g          = head(gs);
        goals tail_gs    = tail(gs);
        if (auto p = g.find_hyp(n)) {
            expr const & h = p->first;
            unsigned i     = p->second;
            buffer<expr> hyps;
            g.get_hyps(hyps);
            hyps.erase(hyps.size() - i - 1);
            if (depends_on(g.get_type(), h)) {
                throw_tactic_exception_if_enabled(s, sstream() << "invalid 'clear' tactic, conclusion depends on '"
                                                  << n << "'");
                return none_proof_state();
            }
            if (auto h2 = depends_on(i, hyps.end() - i, h)) {
                throw_tactic_exception_if_enabled(s, sstream() << "invalid 'clear' tactic, hypothesis '" << *h2
                                                  << "' depends on '" << n << "'");
                return none_proof_state();
            }
            name_generator ngen = s.get_ngen();
            expr new_type = g.get_type();
            expr new_meta = mk_app(mk_metavar(ngen.next(), Pi(hyps, new_type)), hyps);
            goal new_g(new_meta, new_type);
            substitution new_subst = s.get_subst();
            assign(new_subst, g, new_meta);
            proof_state new_s(s, goals(new_g, tail_gs), new_subst, ngen);
            return some_proof_state(new_s);
        } else {
            throw_tactic_exception_if_enabled(s, sstream() << "invalid 'clear' tactic, goal does not have a hypothesis "
                                              << " named '" << n << "'");
            return none_proof_state();
        }
    };
    return tactic01(fn);
}

void initialize_clear_tactic() {
    auto fn = [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
        buffer<name> ns;
        get_tactic_id_list_elements(app_arg(e), ns, "invalid 'clears' tactic, list of identifiers expected");
        tactic r = clear_tactic(ns.back());
        ns.pop_back();
        while (!ns.empty()) {
            r = then(clear_tactic(ns.back()), r);
            ns.pop_back();
        }
        return r;
    };
    register_tac(get_tactic_clear_name(), fn);
    register_tac(get_tactic_clears_name(), fn);
}
void finalize_clear_tactic() {}
}

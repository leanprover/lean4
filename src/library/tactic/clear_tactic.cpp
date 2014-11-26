/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/locals.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
tactic clear_tactic(name const & n) {
    auto fn = [=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
        goals const & gs = s.get_goals();
        if (empty(gs))
            return none_proof_state();
        goal  g          = head(gs);
        goals tail_gs    = tail(gs);
        expr meta        = g.get_meta();
        buffer<expr> locals;
        get_app_args(meta, locals);
        unsigned i = locals.size();
        while (i > 0) {
            --i;
            if (local_pp_name(locals[i]) == n) {
                // found target
                name real_n = mlocal_name(locals[i]);
                for (unsigned j = i+1; j < locals.size(); j++) {
                    if (contains_local(mlocal_type(locals[j]), real_n))
                        return none_proof_state(); // other variables depends on n
                }
                if (contains_local(g.get_type(), real_n))
                    return none_proof_state(); // type depends on n
                buffer<expr> new_locals;
                for (unsigned j = 0; j < i; j++)
                    new_locals.push_back(locals[j]);
                for (unsigned j = i+1; j < locals.size(); j++)
                    new_locals.push_back(locals[j]);
                name_generator ngen = s.get_ngen();
                expr new_meta = mk_app(mk_metavar(ngen.next(), Pi(new_locals, g.get_type())), new_locals);
                goal new_g(new_meta, g.get_type());
                expr val      = Fun(locals, new_meta);
                substitution new_subst = s.get_subst();
                new_subst.assign(g.get_name(), val);
                proof_state new_s(s, goals(new_g, tail_gs), new_subst, ngen);
                return some_proof_state(new_s);
            }
        }
        return none_proof_state();
    };
    return tactic01(fn);
}

void initialize_clear_tactic() {
    register_tac(name({"tactic", "clear"}),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     name n = tactic_expr_to_id(app_arg(e), "invalid 'clear' tactic, argument must be an identifier");
                     return clear_tactic(n);
                 });
    register_tac(name({"tactic", "clear_lst"}),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<name> ns;
                     get_tactic_id_list_elements(app_arg(e), ns, "invalid 'clears' tactic, list of identifiers expected");
                     tactic r = clear_tactic(ns.back());
                     ns.pop_back();
                     while (!ns.empty()) {
                         r = then(clear_tactic(ns.back()), r);
                         ns.pop_back();
                     }
                     return r;
                 });
}
void finalize_clear_tactic() {}
}

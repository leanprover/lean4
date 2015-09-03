/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/elaborate.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
LEAN_THREAD_PTR(proof_state const, g_info_proof_state);

optional<proof_state> get_info_tactic_proof_state() {
    if (g_info_proof_state) {
        return some_proof_state(*g_info_proof_state);
    } else {
        return none_proof_state();
    }
}

void set_info_tactic_proof_state(proof_state const * ps) {
    g_info_proof_state = ps;
}

struct scoped_info_tactic_proof_state {
    scoped_info_tactic_proof_state(proof_state const & s) {
        set_info_tactic_proof_state(&s);
    }
    ~scoped_info_tactic_proof_state() {
        set_info_tactic_proof_state(nullptr);
    }
};

tactic mk_info_tactic(elaborate_fn const & fn, expr const & e) {
    return tactic1([=](environment const &, io_state const & ios, proof_state const & ps) -> proof_state {
            // create dummy variable just to communicate position to the elaborator
            expr dummy = mk_sort(mk_level_zero(), e.get_tag());
            scoped_info_tactic_proof_state scope(ps);
            fn(goal(), ios.get_options(), name_generator("dummy"), dummy, none_expr(), substitution(), false);
            return ps;
        });
}

#define INFO_TAC_NAME name({"tactic", "info"})

expr mk_info_tactic_expr() {
    return mk_constant(INFO_TAC_NAME);
}

void initialize_info_tactic() {
    register_tac(INFO_TAC_NAME,
                 [](type_checker &, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     return mk_info_tactic(fn, e);
                 });
}
void finalize_info_tactic() {
}
}

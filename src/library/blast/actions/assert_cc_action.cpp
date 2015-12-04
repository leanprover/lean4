/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/congruence_closure.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/actions/assert_cc_action.h"

namespace lean {
namespace blast {
action_result assert_cc_action(hypothesis_idx hidx) {
    if (!get_config().m_cc)
        return action_result::failed();
    congruence_closure & cc = get_cc();
    if (has_expr_metavar(curr_state().get_hypothesis_decl(hidx).get_type()))
        return action_result::failed();
    cc.add(hidx);
    // cc.display();
    if (cc.is_inconsistent()) {
        try {
            app_builder & b  = get_app_builder();
            expr false_proof = *cc.get_inconsistency_proof();
            trace_action("contradiction by congruence closure");
            return action_result(b.mk_false_rec(curr_state().get_target(), false_proof));
        } catch (app_builder_exception &) {
            return action_result::failed();
        }
    } else {
        expr const & target = curr_state().get_target();
        name R; expr lhs, rhs;
        if (is_relation_app(target, R, lhs, rhs) && cc.is_eqv(R, lhs, rhs)) {
            expr proof = *cc.get_eqv_proof(R, lhs, rhs);
            trace_action("equivalence by congruence closure");
            return action_result(proof);
        } else if (is_prop(target) && !is_false(target) && cc.proved(target)) {
            expr proof = *cc.get_proof(target);
            trace_action("equivalent to true by congruence closure");
            return action_result(proof);
        } else {
            return action_result::new_branch();
        }
    }
}
}}

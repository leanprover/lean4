/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/assert_cc_action.h"
#include "library/blast/congruence_closure.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"

namespace lean {
namespace blast {
static unsigned g_ext_id = 0;
struct cc_branch_extension : public branch_extension {
    congruence_closure m_cc;
    cc_branch_extension() {}
    cc_branch_extension(cc_branch_extension const & o):m_cc(o.m_cc) {}
    virtual ~cc_branch_extension() {}
    virtual branch_extension * clone() { return new cc_branch_extension(*this); }
};

void initialize_assert_cc_action() {
    g_ext_id = register_branch_extension(new cc_branch_extension());
}

void finalize_assert_cc_action() {}

static congruence_closure & get_cc() {
    return static_cast<cc_branch_extension&>(curr_state().get_extension(g_ext_id)).m_cc;
}

action_result assert_cc_action(hypothesis_idx hidx) {
    congruence_closure & cc = get_cc();
    cc.add(hidx);
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

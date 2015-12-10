/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/strategy.h"
#include "library/blast/simplifier/simplifier_actions.h"
#include "library/blast/actions/simple_actions.h"
#include "library/blast/actions/intros_action.h"
#include "library/blast/actions/subst_action.h"
#include "library/blast/actions/no_confusion_action.h"

namespace lean {
namespace blast {

class simplifier_strategy_fn : public strategy_fn {
    bool m_simp_target;
    bool m_simp_hyps;
    bool m_use_hyps;

    virtual char const * get_name() const override { return "simp"; }

    virtual action_result hypothesis_pre_activation(hypothesis_idx hidx) override {
        Try(assumption_contradiction_actions(hidx));
        if (m_simp_hyps) {
            Try(simplify_hypothesis_action(hidx));
        }
        Try(no_confusion_action(hidx));
        Try(discard_action(hidx));
        if (m_use_hyps)
            Try(subst_action(hidx));
        return action_result::new_branch();
    }

    virtual action_result hypothesis_post_activation(hypothesis_idx hidx) override {
        if (m_use_hyps)
            add_simp_rule_action(hidx);
        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        if (m_simp_hyps || m_use_hyps) {
            Try(intros_action());
            Try(assumption_action());
            Try(activate_hypothesis());
        }
        if (m_simp_target) {
            Try(simplify_target_action());
        }
        Try(trivial_action());
        return action_result::failed();
    }
public:
    simplifier_strategy_fn(bool simp_target, bool simp_hyps, bool use_hyps):
        m_simp_target(simp_target), m_simp_hyps(simp_hyps),
        m_use_hyps(use_hyps) {}
};

strategy mk_simplify_target_strategy() {
    return []() { return simplifier_strategy_fn(true, false, false)(); }; // NOLINT
}

strategy mk_simplify_all_strategy() {
    return []() { return simplifier_strategy_fn(true, true, false)(); }; // NOLINT
}

strategy mk_simplify_using_hypotheses_strategy() {
    return []() { return simplifier_strategy_fn(true, true, true)(); }; // NOLINT
}
}}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/trace.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/choice_point.h"
#include "library/blast/simplifier/simplifier_actions.h"
#include "library/blast/unit/unit_actions.h"
#include "library/blast/actions/simple_actions.h"
#include "library/blast/actions/intros_action.h"
#include "library/blast/actions/subst_action.h"
#include "library/blast/actions/no_confusion_action.h"
#include "library/blast/actions/assert_cc_action.h"
#include "library/blast/actions/recursor_action.h"
#include "library/blast/strategies/preprocess_strategy.h"

namespace lean {
namespace blast {
class preprocess_strategy_fn : public strategy_fn {
    strategy m_main;
    bool     m_simple;
    bool     m_done{false};

    virtual bool show_failure() const override { return false; }

    virtual char const * get_name() const override { return "preprocessor"; }

    virtual action_result hypothesis_pre_activation(hypothesis_idx hidx) override {
        Try(assumption_contradiction_actions(hidx));
        Try(simplify_hypothesis_action(hidx));
        if (!m_simple)
            Try(unit_preprocess(hidx));
        Try(no_confusion_action(hidx));
        if (!m_simple)
            TrySolve(assert_cc_action(hidx));
        Try(discard_action(hidx));
        Try(subst_action(hidx));
        return action_result::new_branch();
    }

    virtual action_result hypothesis_post_activation(hypothesis_idx hidx) override {
        if (!m_simple) {
            Try(unit_propagate(hidx));
            Try(recursor_preprocess_action(hidx));
        }
        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        if (!m_done) {
            Try(intros_action());
            Try(assumption_action());
            Try(activate_hypothesis());
            Try(simplify_target_action());
            m_done = true;
        }
        if (get_num_choice_points() > get_initial_num_choice_points())
            throw exception("invalid blast preprocessing action, preprocessing actions should not create choice points");
        if (optional<expr> pf = m_main()) {
            return action_result::solved(*pf);
        }
        return action_result::failed();
    }
public:
    preprocess_strategy_fn(strategy const & S, bool simple):
        m_main(S), m_simple(simple) {}
};

strategy preprocess_and_then(strategy const & S) {
    return [=]() { return preprocess_strategy_fn(S, false)(); }; // NOLINT
}

strategy basic_preprocess_and_then(strategy const & S) {
    return [=]() { return preprocess_strategy_fn(S, true)(); }; // NOLINT
}
}}

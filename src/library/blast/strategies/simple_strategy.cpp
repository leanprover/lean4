/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/blast.h"
#include "library/blast/options.h"
#include "library/blast/choice_point.h"
#include "library/blast/proof_expr.h"
#include "library/blast/strategy.h"
#include "library/blast/trace.h"
#include "library/blast/simplifier/simplifier_actions.h"
#include "library/blast/backward/backward_action.h"
#include "library/blast/backward/backward_strategy.h"
#include "library/blast/forward/forward_actions.h"
#include "library/blast/forward/ematch.h"
#include "library/blast/unit/unit_actions.h"
#include "library/blast/actions/simple_actions.h"
#include "library/blast/actions/intros_action.h"
#include "library/blast/actions/subst_action.h"
#include "library/blast/actions/recursor_action.h"
#include "library/blast/actions/by_contradiction_action.h"
#include "library/blast/actions/assert_cc_action.h"
#include "library/blast/actions/no_confusion_action.h"

namespace lean {
namespace blast {
/** \brief Implement a simple proof strategy for blast.
    We use it mainly for testing new actions and the whole blast infra-structure. */
class simple_strategy_fn : public strategy_fn {
    virtual char const * get_name() const override { return "simple"; }

    virtual action_result hypothesis_pre_activation(hypothesis_idx hidx) override {
        Try(assumption_contradiction_actions(hidx));
        Try(simplify_hypothesis_action(hidx));
        Try(unit_preprocess(hidx));
        Try(no_confusion_action(hidx));
        TrySolve(assert_cc_action(hidx));
        Try(discard_action(hidx));
        Try(subst_action(hidx));
        return action_result::new_branch();
    }

    virtual action_result hypothesis_post_activation(hypothesis_idx hidx) override {
        Try(unit_propagate(hidx));
        Try(recursor_preprocess_action(hidx));
        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        Try(intros_action());
        Try(activate_hypothesis());
        Try(trivial_action());
        Try(assumption_action());
        Try(recursor_action());
        Try(ematch_action());
        Try(constructor_action());
        Try(by_contradiction_action());
        TryStrategy(mk_backward_strategy());
        Try(qfc_action(list<gexpr>()));
        return action_result::failed();
    }
};

strategy mk_simple_strategy() {
    return []() { return simple_strategy_fn()(); }; // NOLINT
}
}}

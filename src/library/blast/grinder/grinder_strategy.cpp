/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/unit/unit_actions.h"
#include "library/blast/actions/simple_actions.h"
#include "library/blast/actions/intros_action.h"
#include "library/blast/actions/subst_action.h"
#include "library/blast/actions/no_confusion_action.h"
#include "library/blast/actions/assert_cc_action.h"
#include "library/blast/grinder/grinder_strategy.h"
#include "library/blast/grinder/grinder_actions.h"

namespace lean {
namespace blast {
action_result grinder_strategy_core_fn::hypothesis_pre_activation(hypothesis_idx hidx) {
    Try(assumption_contradiction_actions(hidx));
    Try(no_confusion_action(hidx));
    TrySolve(assert_cc_action(hidx));
    Try(discard_action(hidx));
    Try(subst_action(hidx));
    Try(pre(hidx));
    return action_result::new_branch();
}

action_result grinder_strategy_core_fn::hypothesis_post_activation(hypothesis_idx hidx) {
    Try(unit_propagate(hidx));
    Try(grinder_elim_action(hidx));
    Try(post(hidx));
    return action_result::new_branch();
}

action_result grinder_strategy_core_fn::next_action() {
    Try(intros_action());
    Try(assumption_action());
    Try(activate_hypothesis());
    Try(grinder_intro_action());
    Try(next());
    return action_result::failed();
}

strategy grind_and_then(strategy const & S) {
    return [=]() { // NOLINT
        curr_state().deactivate_all();
        return grinder_strategy_fn([](hypothesis_idx) { return action_result::failed(); }, // NOLINT
                                   [](hypothesis_idx) { return action_result::failed(); }, // NOLINT
                                   [=]() { // NOLINT
                                       if (optional<expr> pf = S()) {
                                           return action_result::solved(*pf);
                                       }
                                       return action_result::failed();
                                   })();
    };
}
}}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/blast.h"
#include "library/blast/options.h"
#include "library/blast/choice_point.h"
#include "library/blast/simple_actions.h"
#include "library/blast/proof_expr.h"
#include "library/blast/intros_action.h"
#include "library/blast/subst_action.h"
#include "library/blast/backward_action.h"
#include "library/blast/no_confusion_action.h"
#include "library/blast/simplify_actions.h"
#include "library/blast/recursor_action.h"
#include "library/blast/strategy.h"

namespace lean {
namespace blast {
/** \brief Implement a simple proof strategy for blast.
    We use it mainly for testing new actions and the whole blast infra-structure. */
class simple_strategy : public strategy {
    action_result activate_hypothesis(bool preprocess) {
        auto hidx = curr_state().activate_hypothesis();
        if (!hidx) return action_result::failed();

        if (!preprocess) display_action("activate");

        if (auto pr = assumption_contradiction_actions(*hidx)) {
            if (!preprocess) display_action("assumption-contradiction");
            return action_result::solved(*pr);
        }

        if (subst_action(*hidx)) {
            if (!preprocess) display_action("subst");
            return action_result::new_branch();
        }

        action_result r = no_confusion_action(*hidx);
        if (!failed(r)) {
            if (!preprocess) display_action("no_confusion");
            return r;
        }

        if (discard(*hidx)) {
            if (!preprocess) display_action("discard redudant hypothesis");
            curr_state().del_hypothesis(*hidx);
            return action_result::new_branch();
        }

        if (optional<name> R = is_recursor_action_target(*hidx)) {
            unsigned num_minor = get_num_minor_premises(*R);
            if (num_minor == 1) {
                action_result r = recursor_action(*hidx, *R);
                if (!failed(r)) {
                    if (!preprocess) display_action("recursor");
                    return r;
                }
            } else {
                // If the hypothesis recursor has more than 1 minor premise, we
                // put it in a priority queue.
                // TODO(Leo): refine

                // TODO(Leo): the following weight computation is too simple...
                double w = 1.0 / (static_cast<double>(*hidx) + 1.0);
                if (!is_recursive_recursor(*R)) {
                    // TODO(Leo): we need a better strategy for handling recursive recursors...
                    w += static_cast<double>(num_minor);
                    curr_state().add_to_rec_queue(*hidx, w);
                }
            }
        }

        return action_result::new_branch();
    }

    /* \brief Preprocess state
       It keeps applying intros, activating and finally simplify target.
       Return an expression if the goal has been proved during preprocessing step. */
    virtual optional<expr> preprocess() {
        display_msg("* Preprocess");
        while (true) {
            if (intros_action())
                continue;
            auto r = activate_hypothesis(true);
            if (solved(r)) return r.to_opt_expr();
            if (failed(r)) break;
        }
        if (auto pr = assumption_action())
            return pr;
        return simplify_target_action().to_opt_expr();
    }

    virtual action_result next_action() {
        if (intros_action()) {
            display_action("intros");
            return action_result::new_branch();
        }

        action_result r = activate_hypothesis(false);
        if (!failed(r)) return r;

        if (auto pr = trivial_action()) {
            display_action("trivial");
            return action_result::solved(*pr);
        }

        if (auto pr = assumption_action()) {
            // Remark: this action is only relevant
            // when the target has been modified.
            display_action("assumption");
            return action_result::solved(*pr);
        }

        while (auto hidx = curr_state().select_rec_hypothesis()) {
            if (optional<name> R = is_recursor_action_target(*hidx)) {
                r = recursor_action(*hidx, *R);
                if (!failed(r)) {
                    display_action("recursor");
                    return r;
                }
            }
        }

        r = constructor_action();
        if (!failed(r)) {
            display_action("constructor");
            return r;
        }

        // TODO(Leo): add more actions...

        display_msg(">>> FAILED <<<");
        return action_result::failed();
    }
};

optional<expr> apply_simple_strategy() {
    return simple_strategy()();
}
}}

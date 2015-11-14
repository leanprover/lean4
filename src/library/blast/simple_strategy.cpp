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

namespace lean {
namespace blast {
/** \brief Implement a simple proof strategy for blast.
    We use it mainly for testing new actions and the whole blast infra-structure. */
class simple_strategy {
    config m_config;

    enum status { NoAction, ClosedBranch, Continue };

    void display_msg(char const * msg) {
        if (m_config.m_trace) {
            ios().get_diagnostic_channel() << msg << "\n\n";
        }
    }

    void display_action(char const * name) {
        if (m_config.m_trace) {
            ios().get_diagnostic_channel() << "== action: " << name << " ==>\n\n";
        }
    }

    void display() {
        if (m_config.m_trace) {
            auto out = diagnostic(env(), ios());
            out << "state [" << curr_state().get_proof_depth() << "], #choice: " << get_num_choice_points() << "\n";
            display_curr_state();
        }
    }

    void display_if(action_result r) {
        if (m_config.m_trace && !failed(r))
            display();
    }

    optional<hypothesis_idx> activate_hypothesis() {
        return curr_state().activate_hypothesis();
    }

    /* \brief Preprocess state
       It keeps applying intros, activating and finally simplify target.
       Return an expression if the goal has been proved during preprocessing step. */
    optional<expr> preprocess_core() {
        display_msg("* Preprocess");
        while (true) {
            if (intros_action())
                continue;
            if (auto hidx = activate_hypothesis()) {
                if (auto pr = assumption_contradiction_actions(*hidx)) {
                    return pr;
                }
                if (subst_action(*hidx))
                    continue;
                action_result r = no_confusion_action(*hidx);
                if (solved(r))
                    return r.to_opt_expr();
                continue;
            }
            break;
        }
        if (auto pr = assumption_action())
            return pr;
        return simplify_target_action().to_opt_expr();
    }

    optional<expr> preprocess() {
        if (auto pr = preprocess_core()) {
            auto r = next_branch(*pr);
            if (!solved(r)) {
                throw exception("invalid blast preprocessing action, preprocessing actions should not create branches");
            } else {
                return r.to_opt_expr();
            }
        } else {
            return none_expr();
        }
    }

    action_result next_action() {
        if (intros_action()) {
            display_action("intros");
            return action_result::new_branch();
        }

        if (auto hidx = activate_hypothesis()) {
            display_action("activate");
            if (auto pr = assumption_contradiction_actions(*hidx)) {
                display_action("assumption-contradiction");
                return action_result::solved(*pr);
            }
            if (subst_action(*hidx)) {
                display_action("subst");
                return action_result::new_branch();
            }
            action_result r = no_confusion_action(*hidx);
            if (!failed(r)) {
                display_action("no_confusion");
                return r;
            }
            return action_result::new_branch();
        }

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

        action_result r = constructor_action();
        if (!failed(r)) {
            display_action("constructor");
            return r;
        }

        // TODO(Leo): add more actions...

        display_msg(">>> FAILED <<<");
        return action_result::failed();
    }

    action_result next_branch(expr pr) {
        while (curr_state().has_proof_steps()) {
            proof_step s     = curr_state().top_proof_step();
            action_result r  = s.resolve(unfold_hypotheses_ge(curr_state(), pr));
            switch (r.get_kind()) {
            case action_result::Failed:
                display_msg(">>> next-branch FAILED <<<");
                return r;
            case action_result::Solved:
                pr = r.get_proof();
                curr_state().pop_proof_step();
                break;
            case action_result::NewBranch:
                return action_result::new_branch();
            }
        }
        return action_result::solved(pr);
    }

    optional<expr> search_upto(unsigned depth) {
        if (m_config.m_trace) {
            ios().get_diagnostic_channel() << "* Search upto depth " << depth << "\n\n";
        }
        display();
        action_result r = next_action();
        display_if(r);
        while (true) {
            lean_assert(curr_state().check_invariant());
            if (curr_state().get_proof_depth() > depth) {
                display_msg(">>> maximum search depth reached <<<");
                r = action_result::failed();
            }
            switch (r.get_kind()) {
            case action_result::Failed:
                r = next_choice_point();
                if (failed(r)) {
                    // all choice points failed...
                    display_msg(">>> proof not found, no choice points left <<<");
                    return none_expr();
                }
                display_msg("* next choice point");
                break;
            case action_result::Solved:
                r = next_branch(r.get_proof());
                if (r.get_kind() == action_result::Solved) {
                    // all branches have been solved
                    display_msg("* found proof");
                    return some_expr(r.get_proof());
                }
                display_msg("* next branch");
                break;
            case action_result::NewBranch:
                r = next_action();
                break;
            }
            display_if(r);
        }
    }

    optional<expr> search() {
        clear_choice_points();
        curr_state().set_simp_rule_sets(get_simp_rule_sets(env()));
        if (auto pr = preprocess())
            return pr;
        if (get_num_choice_points() > 0)
            throw exception("invalid blast preprocessing action, preprocessing actions should not create choice points");
        state s    = curr_state();
        unsigned d = m_config.m_init_depth;
        while (true) {
            if (auto r = search_upto(d))
                return r;
            d += m_config.m_inc_depth;
            if (d > m_config.m_max_depth) {
                display_curr_state();
                return none_expr();
            }
            curr_state() = s;
            clear_choice_points();
        }
    }

public:
    simple_strategy():
        m_config(ios().get_options()) {
    }

    optional<expr> operator()() {
        return search();
    }
};

optional<expr> apply_simple_strategy() {
    return simple_strategy()();
}
}}

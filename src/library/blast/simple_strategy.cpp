/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/blast.h"
#include "library/blast/options.h"
#include "library/blast/choice_point.h"
#include "library/blast/simple_actions.h"
#include "library/blast/intros.h"
#include "library/blast/backward.h"

namespace lean {
namespace blast {
/** \brief Implement a simple proof strategy for blast.
    We use it mainly for testing new actions and the whole blast infra-structure. */
class simple_strategy {
    unsigned                   m_max_depth;
    unsigned                   m_init_depth;
    unsigned                   m_inc_depth;

    enum status { NoAction, ClosedBranch, Continue };

    optional<hypothesis_idx> activate_hypothesis() {
        return curr_state().activate_hypothesis();
    }

    action_result next_action() {
        if (intros_action())
            return action_result::new_branch();

        if (auto hidx = activate_hypothesis()) {
            if (auto pr = assumption_contradiction_actions(*hidx))
                return action_result::solved(*pr);
            return action_result::new_branch();
        }

        if (auto pr = assumption_action()) {
            // Remark: this action is only relevant
            // when the target has been modified.
            return action_result::solved(*pr);
        }

        action_result r = constructor_action();
        if (!failed(r)) return r;

        // TODO(Leo): add more actions...
        return action_result::failed();
    }

    action_result next_branch(expr pr) {
        while (curr_state().has_proof_steps()) {
            proof_step s     = curr_state().top_proof_step();
            action_result r = s.resolve(pr);
            switch (r.get_kind()) {
            case action_result::Failed:
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
        action_result r = next_action();
        while (true) {
            if (curr_state().get_proof_depth() > depth)
                r = action_result::failed();
            switch (r.get_kind()) {
            case action_result::Failed:
                r = next_choice_point();
                if (failed(r)) {
                    // all choice points failed...
                    return none_expr();
                }
                break;
            case action_result::Solved:
                r = next_branch(r.get_proof());
                if (r.get_kind() == action_result::Solved) {
                    // all branches have been solved
                    return some_expr(r.get_proof());
                }
                break;
            case action_result::NewBranch:
                r = next_action();
                break;
            }
        }
    }

    optional<expr> search() {
        state s    = curr_state();
        unsigned d = m_init_depth;
        while (true) {
            if (auto r = search_upto(d))
                return r;
            d += m_inc_depth;
            if (d > m_max_depth) {
                display_curr_state();
                return none_expr();
            }
            curr_state() = s;
            clear_choice_points();
        }
    }

public:
    simple_strategy() {
        options o = ios().get_options();
        m_max_depth  = get_blast_max_depth(o);
        m_init_depth = get_blast_init_depth(o);
        m_inc_depth  = get_blast_inc_depth(o);
    }

    optional<expr> operator()() {
        return search();
    }
};

optional<expr> apply_simple_strategy() {
    return simple_strategy()();
}
}}

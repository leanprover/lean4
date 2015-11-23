/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/strategy.h"
#include "library/blast/choice_point.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"
#include "library/blast/trace.h"

namespace lean {
namespace blast {
strategy::strategy() {}

action_result strategy::activate_hypothesis(bool preprocess) {
    scope_trace scope(!preprocess && get_config().m_trace);
    auto hidx = curr_state().select_hypothesis_to_activate();
    if (!hidx) return action_result::failed();
    auto r    = hypothesis_pre_activation(*hidx);
    if (!solved(r) && !failed(r)) {
        curr_state().activate_hypothesis(*hidx);
        return hypothesis_post_activation(*hidx);
    } else {
        return r;
    }
}

action_result strategy::next_branch(expr pr) {
    while (curr_state().has_proof_steps()) {
        proof_step s     = curr_state().top_proof_step();
        action_result r  = s.resolve(unfold_hypotheses_ge(curr_state(), pr));
        switch (r.get_kind()) {
        case action_result::Failed:
            trace(">>> next-branch FAILED <<<");
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

optional<expr> strategy::search_upto(unsigned depth) {
    if (is_trace_enabled()) {
        ios().get_diagnostic_channel() << "* Search upto depth " << depth << "\n\n";
    }
    trace_curr_state();
    action_result r = next_action();
    trace_curr_state_if(r);
    while (true) {
        lean_assert(curr_state().check_invariant());
        if (curr_state().get_proof_depth() > depth) {
            trace(">>> maximum search depth reached <<<");
            r = action_result::failed();
        }
        switch (r.get_kind()) {
        case action_result::Failed:
            r = next_choice_point(m_init_num_choices);
            if (failed(r)) {
                // all choice points failed...
                trace(">>> proof not found, no choice points left <<<");
                return none_expr();
            }
            trace("* next choice point");
            break;
        case action_result::Solved:
            r = next_branch(r.get_proof());
            if (r.get_kind() == action_result::Solved) {
                // all branches have been solved
                trace("* found proof");
                return some_expr(r.get_proof());
            }
            trace("* next branch");
            break;
        case action_result::NewBranch:
            r = next_action();
            break;
        }
        trace_curr_state_if(r);
    }
}

optional<expr> strategy::invoke_preprocess() {
    if (auto pr = preprocess()) {
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

optional<expr> strategy::search() {
    scope_choice_points scope1;
    curr_state().clear_proof_steps();
    m_init_num_choices = get_num_choice_points();
    if (auto pr = invoke_preprocess())
        return pr;
    if (get_num_choice_points() > m_init_num_choices)
        throw exception("invalid blast preprocessing action, preprocessing actions should not create choice points");
    state s    = curr_state();
    unsigned d = get_config().m_init_depth;
    while (true) {
        if (auto r = search_upto(d))
            return r;
        d += get_config().m_inc_depth;
        if (d > get_config().m_max_depth) {
            if (get_config().m_show_failure)
                display_curr_state();
            return none_expr();
        }
        curr_state() = s;
        shrink_choice_points(m_init_num_choices);
    }
}
}}

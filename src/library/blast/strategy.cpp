/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/interrupt.h"
#include "library/trace.h"
#include "library/blast/strategy.h"
#include "library/blast/choice_point.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"
#include "library/blast/trace.h"

namespace lean {
namespace blast {
strategy_fn::strategy_fn() {}

action_result strategy_fn::activate_hypothesis() {
    auto hidx = curr_state().select_hypothesis_to_activate();
    if (!hidx) return action_result::failed();
    auto r    = hypothesis_pre_activation(*hidx);
    // The pre-activation may delete the hypothesis (e.g., subsumption)
    if (!solved(r) && !failed(r) && !curr_state().get_hypothesis_decl(*hidx).is_dead()) {
        curr_state().activate_hypothesis(*hidx);
        return hypothesis_post_activation(*hidx);
    } else {
        return r;
    }
}

action_result strategy_fn::next_branch(expr pr) {
    while (m_ps_check_point.has_new_proof_steps(curr_state())) {
        proof_step s     = curr_state().top_proof_step();
        action_result r  = s.resolve(unfold_hypotheses_ge(curr_state(), pr));
        switch (r.get_kind()) {
        case action_result::Failed:
            trace_search(">>> next-branch FAILED <<<");
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

bool strategy_fn::show_failure() const {
    return get_config().m_show_failure;
}

optional<expr> strategy_fn::search() {
    scope_choice_points scope1;
    m_ps_check_point          = curr_state().mk_proof_steps_check_point();
    m_init_num_choices        = get_num_choice_points();
    unsigned init_proof_depth = curr_state().get_proof_depth();
    unsigned max_depth        = get_config().m_max_depth;
    lean_trace_search(tout() << "begin '" << get_name() << "' strategy (max-depth: " << max_depth << ")\n";);
    trace_curr_state();
    trace_target();
    action_result r = next_action();
    trace_curr_state_if(r);
    while (true) {
        check_system("blast");
        lean_assert(curr_state().check_invariant());
        if (curr_state().get_proof_depth() > max_depth) {
            trace_search(">>> maximum search depth reached <<<");
            r = action_result::failed();
        }
        switch (r.get_kind()) {
        case action_result::Failed:
            lean_trace_deadend(tout() << "strategy '" << get_name() << "'\n"; curr_state().display(tout()););
            r = next_choice_point(m_init_num_choices);
            if (failed(r)) {
                // all choice points failed...
                lean_trace_search(tout() << "strategy '" << get_name() << "' failed, no proof found\n";);
                if (show_failure())
                    display_curr_state();
                return none_expr();
            }
            break;
        case action_result::Solved:
            r = next_branch(r.get_proof());
            if (r.get_kind() == action_result::Solved) {
                // all branches have been solved
                lean_trace_search(tout() << "strategy '" << get_name() << "' succeeded, proof found\n";);
                return some_expr(unfold_hypotheses_ge(curr_state(), r.get_proof(), init_proof_depth));
            }
            break;
        case action_result::NewBranch:
            r = next_action();
            break;
        }
        trace_depth_nchoices();
        trace_curr_state_if(r);
        trace_target();
    }
}

strategy operator||(strategy const & s1, strategy const & s2) {
    return [=]() { // NOLINT
        if (auto r = s1())
            return r;
        else
            return s2();
    };
}
}}

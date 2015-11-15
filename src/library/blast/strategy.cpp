/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/strategy.h"
#include "library/blast/choice_point.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"

namespace lean {
namespace blast {
strategy::strategy():
    m_config(ios().get_options()) {
}

void strategy::display_msg(char const * msg) {
    if (m_config.m_trace) {
        ios().get_diagnostic_channel() << msg << "\n\n";
    }
}

void strategy::display_action(char const * name) {
    if (m_config.m_trace) {
        ios().get_diagnostic_channel() << "== action: " << name << " ==>\n\n";
    }
}

void strategy::display() {
    if (m_config.m_trace) {
        auto out = diagnostic(env(), ios());
        out << "state [" << curr_state().get_proof_depth() << "], #choice: " << get_num_choice_points() << "\n";
        display_curr_state();
    }
}

void strategy::display_if(action_result r) {
    if (m_config.m_trace && !failed(r))
        display();
}

action_result strategy::next_branch(expr pr) {
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

optional<expr> strategy::search_upto(unsigned depth) {
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
            r = next_choice_point(m_init_num_choices);
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
    m_init_num_choices = get_num_choice_points();
    curr_state().set_simp_rule_sets(get_simp_rule_sets(env()));
    if (auto pr = invoke_preprocess())
        return pr;
    if (get_num_choice_points() > m_init_num_choices)
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
        shrink_choice_points(m_init_num_choices);
    }
}
}}

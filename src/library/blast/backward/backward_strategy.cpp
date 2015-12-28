/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "library/attribute_manager.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/choice_point.h"
#include "library/blast/proof_expr.h"
#include "library/blast/strategy.h"
#include "library/blast/backward/backward_lemmas.h"
#include "library/blast/backward/backward_action.h"
#include "library/blast/actions/simple_actions.h"
#include "library/blast/actions/intros_action.h"
#include "library/blast/actions/no_confusion_action.h"
#include "library/blast/actions/subst_action.h"

namespace lean {
namespace blast {
static unsigned g_ext_id = 0;
struct backward_branch_extension : public branch_extension {
    backward_lemma_index m_backward_lemmas;
    backward_branch_extension() {}
    backward_branch_extension(backward_branch_extension const & b):
        m_backward_lemmas(b.m_backward_lemmas) {}
    virtual ~backward_branch_extension() {}
    virtual branch_extension * clone() override { return new backward_branch_extension(*this); }
    virtual void initialized() override { m_backward_lemmas.init(); }
    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx) override {
        m_backward_lemmas.insert(h.get_self());
    }
    virtual void hypothesis_deleted(hypothesis const & h, hypothesis_idx) override {
        m_backward_lemmas.erase(h.get_self());
    }
    backward_lemma_index const & get_backward_lemmas() const { return m_backward_lemmas; }
};

void initialize_backward_strategy() {
    g_ext_id = register_branch_extension(new backward_branch_extension());
}

void finalize_backward_strategy() {
}

static backward_branch_extension & get_extension() {
    return static_cast<backward_branch_extension&>(curr_state().get_extension(g_ext_id));
}

/** \brief Basic backwards chaining, inspired by Coq's [auto]. */
class backward_strategy_fn : public strategy_fn {
    virtual char const * get_name() const override { return "backward"; }

    virtual action_result hypothesis_pre_activation(hypothesis_idx hidx) override {
        Try(assumption_contradiction_actions(hidx));
        Try(subst_action(hidx));
        Try(no_confusion_action(hidx));
        Try(discard_action(hidx));
        return action_result::new_branch();
    }

    virtual action_result hypothesis_post_activation(hypothesis_idx) override {
        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        Try(intros_action());
        Try(activate_hypothesis());
        Try(trivial_action());
        Try(assumption_action());
        list<gexpr> backward_rules = get_extension().get_backward_lemmas().find(head_index(curr_state().get_target()));
        Try(backward_action(backward_rules, true));
        return action_result::failed();
    }
};

strategy mk_backward_strategy() {
    if (!get_config().m_backward)
        return []() { return none_expr(); }; // NOLINT
    else
        return []() { // NOLINT
            flet<bool> disable_show_failure(get_config().m_show_failure, false);
            return backward_strategy_fn()();
        };
}
}}

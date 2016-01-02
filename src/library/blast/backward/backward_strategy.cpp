/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "util/sexpr/option_declarations.h"
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

#ifndef LEAN_DEFAULT_BLAST_BACKWARD_MAX_ROUNDS
#define LEAN_DEFAULT_BLAST_BACKWARD_MAX_ROUNDS 8
#endif

namespace lean {
namespace blast {
static name * g_blast_backward_max_rounds = nullptr;

unsigned get_blast_backward_max_rounds(options const & o) {
    return o.get_unsigned(*g_blast_backward_max_rounds, LEAN_DEFAULT_BLAST_BACKWARD_MAX_ROUNDS);
}

static unsigned g_ext_id = 0;
struct backward_branch_extension : public branch_extension {
    backward_lemma_index m_backward_lemmas;
    unsigned             m_num_rounds{0};

    backward_branch_extension() {}
    backward_branch_extension(backward_branch_extension const & b):
        m_backward_lemmas(b.m_backward_lemmas), m_num_rounds(b.m_num_rounds) {}
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
    g_blast_backward_max_rounds = new name{"blast", "backward", "max_rounds"};
    register_unsigned_option(*blast::g_blast_backward_max_rounds, LEAN_DEFAULT_BLAST_BACKWARD_MAX_ROUNDS,
                             "(blast) maximum number of nested backward chaining steps");
}

void finalize_backward_strategy() {
    delete g_blast_backward_max_rounds;
}

static backward_branch_extension & get_extension() {
    return static_cast<backward_branch_extension&>(curr_state().get_extension(g_ext_id));
}

/** \brief Basic backwards chaining, inspired by Coq's [auto]. */
class backward_strategy_fn : public strategy_fn {
    unsigned m_max_rounds;

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
        auto & ext = get_extension();
        if (ext.m_num_rounds < m_max_rounds) {
            list<gexpr> backward_rules = ext.get_backward_lemmas().find(head_index(curr_state().get_target()));
            ext.m_num_rounds++;
            Try(backward_action(backward_rules, true));
        }
        return action_result::failed();
    }
public:
    backward_strategy_fn(unsigned max_rounds):m_max_rounds(max_rounds) {}
};

strategy mk_backward_strategy() {
    if (!get_config().m_backward)
        return []() { return none_expr(); }; // NOLINT
    return []() { // NOLINT
        unsigned max_rounds = get_blast_backward_max_rounds(ios().get_options());
        return backward_strategy_fn(max_rounds)();
    };
}
}}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/actions/recursor_action.h"
#include "library/blast/backward/backward_action.h"
#include "library/blast/grinder/intro_elim_lemmas.h"

namespace lean {
namespace blast {
static unsigned g_ext_id = 0;

struct grinder_branch_extension : public branch_extension {
    head_map<gexpr> m_intro_lemmas;
    name_map<name>  m_elim_lemmas;

    grinder_branch_extension() {}
    grinder_branch_extension(grinder_branch_extension const & e):
        m_intro_lemmas(e.m_intro_lemmas),
        m_elim_lemmas(e.m_elim_lemmas) {}
    virtual ~grinder_branch_extension() {}
    virtual branch_extension * clone() override { return new grinder_branch_extension(*this); }
    virtual void initialized() override {
        m_intro_lemmas = mk_intro_lemma_index();
        m_elim_lemmas  = mk_elim_lemma_index();
    }
};

void initialize_grinder_actions() {
    g_ext_id = register_branch_extension(new grinder_branch_extension());
}

void finalize_grinder_actions() {}

static grinder_branch_extension & get_ext() {
    return static_cast<grinder_branch_extension&>(curr_state().get_extension(g_ext_id));
}

action_result grinder_elim_action(hypothesis_idx hidx) {
    grinder_branch_extension & ext = get_ext();
    state & s                      = curr_state();
    hypothesis const & h           = s.get_hypothesis_decl(hidx);
    expr const & f                 = get_app_fn(h.get_type());
    if (!is_constant(f))
        return action_result::failed();
    auto R = ext.m_elim_lemmas.find(const_name(f));
    if (!R)
        return action_result::failed();
    return recursor_action(hidx, *R);
}

action_result grinder_intro_action() {
    grinder_branch_extension & ext = get_ext();
    state & s                      = curr_state();
    expr const & target            = s.get_target();
    expr const & f                 = get_app_fn(target);
    if (!is_constant(f))
        return action_result::failed();
    list<gexpr> const * lemmas = ext.m_intro_lemmas.find(head_index(f));
    if (!lemmas)
        return action_result::failed();
    return backward_cut_action(*lemmas);
}
}}

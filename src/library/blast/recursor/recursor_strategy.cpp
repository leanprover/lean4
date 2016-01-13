/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "kernel/inductive/inductive.h"
#include "library/user_recursors.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/choice_point.h"
#include "library/blast/actions/intros_action.h"
#include "library/blast/recursor/recursor_action.h"
#include "library/blast/recursor/recursor_strategy.h"

#ifndef LEAN_DEFAULT_BLAST_RECURSION_MAX_ROUNDS
#define LEAN_DEFAULT_BLAST_RECURSION_MAX_ROUNDS 3
#endif

#ifndef LEAN_DEFAULT_BLAST_RECURSION_STRUCTURE
#define LEAN_DEFAULT_BLAST_RECURSION_STRUCTURE false
#endif

#ifndef LEAN_DEFAULT_BLAST_RECURSION_CLASS
#define LEAN_DEFAULT_BLAST_RECURSION_CLASS false
#endif

namespace lean {
namespace blast {
static name * g_blast_recursion_max_rounds    = nullptr;
static name * g_blast_recursion_structure     = nullptr;
static name * g_blast_recursion_class         = nullptr;

unsigned get_blast_recursion_max_rounds(options const & o) {
    return o.get_unsigned(*g_blast_recursion_max_rounds, LEAN_DEFAULT_BLAST_RECURSION_MAX_ROUNDS);
}

bool get_blast_recursion_structure(options const & o) {
    return o.get_bool(*g_blast_recursion_structure, LEAN_DEFAULT_BLAST_RECURSION_STRUCTURE);
}

bool get_blast_recursion_class(options const & o) {
    return o.get_bool(*g_blast_recursion_class, LEAN_DEFAULT_BLAST_RECURSION_CLASS);
}

void initialize_recursor_strategy() {
    g_blast_recursion_max_rounds = new name{"blast", "recursion", "max_rounds"};
    g_blast_recursion_structure  = new name{"blast", "recursion", "structure"};
    g_blast_recursion_class      = new name{"blast", "recursion", "class"};
    register_unsigned_option(*blast::g_blast_recursion_max_rounds, LEAN_DEFAULT_BLAST_RECURSION_MAX_ROUNDS,
                             "(blast) maximum number of nested recursion/induction steps");
    register_bool_option(*blast::g_blast_recursion_structure, LEAN_DEFAULT_BLAST_RECURSION_STRUCTURE,
                         "(blast) if true recursion strategy also considers inductive types with only one constructor");
    register_bool_option(*blast::g_blast_recursion_class, LEAN_DEFAULT_BLAST_RECURSION_CLASS,
                         "(blast) if true recursion strategy also considers inductive types that are marked as type classes");
}

void finalize_recursor_strategy() {
    delete g_blast_recursion_max_rounds;
    delete g_blast_recursion_structure;
    delete g_blast_recursion_class;
}

static action_result try_hypothesis(hypothesis_idx hidx) {
    state & s = curr_state();
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    expr const & type    = h.get_type();
    expr const & I       = get_app_fn(type);
    lean_assert(is_constant(I));
    name const & I_name  = const_name(I);
    list<name> Rs = get_recursors_for(env(), const_name(I));
    if (Rs) {
        return recursor_action(hidx, head(Rs));
    }
    if (inductive::is_inductive_decl(env(), I_name)) {
        return recursor_action(hidx, inductive::get_elim_name(I_name));
    }
    return action_result::failed();
}

class rec_choice_point_cell : public choice_point_cell {
    state                m_state;
    list<hypothesis_idx> m_hs;
    unsigned             m_choice_idx;
public:
    rec_choice_point_cell(state const & s, list<hypothesis_idx> const & hs, unsigned choice_idx):
        m_state(s), m_hs(hs), m_choice_idx(choice_idx) {}

    virtual action_result next() {
        while (!empty(m_hs)) {
            curr_state()        = m_state;
            hypothesis_idx hidx = head(m_hs);
            m_hs                = tail(m_hs);
            action_result r     = try_hypothesis(hidx);
            if (!failed(r)) {
                lean_trace_search(tout() << "next of choice #" << m_choice_idx
                                  << ", recurse " << ppb(mk_href(hidx)) << "\n";);
                return r;
            }
        }
        return action_result::failed();
    }
};

action_result rec_action(rec_candidate_selector const & selector) {
    hypothesis_idx_buffer hidxs;
    selector(hidxs);
    if (hidxs.empty())
        return action_result::failed();
    if (hidxs.size() == 1)
        return try_hypothesis(hidxs[0]);
    state s = curr_state();
    list<hypothesis_idx> hidx_list = to_list(hidxs);
    while (!empty(hidx_list)) {
        hypothesis_idx hidx = head(hidx_list);
        action_result r     = try_hypothesis(hidx);
        hidx_list           = tail(hidx_list);
        if (!failed(r)) {
            if (!empty(hidx_list)) {
                // create choice point
                unsigned cidx = mk_choice_point_idx();
                push_choice_point(choice_point(new rec_choice_point_cell(s, hidx_list, cidx)));
                lean_trace_search(tout() << "recurse " << ppb(mk_href(hidx)) << " (choice #" << cidx << ")\n";);
            } else {
                lean_trace_search(tout() << "recurse " << ppb(mk_href(hidx)) << "\n";);
            }
            return r;
        }
        curr_state() = s;
    }
    return action_result::failed();
}

class rec_strategy_fn : public strategy_fn {
    strategy               m_S;
    rec_candidate_selector m_selector;
    unsigned               m_init_depth;
    unsigned               m_max_depth;

    virtual bool show_failure() const override { return false; }
    virtual char const * get_name() const override { return "recursor"; }

    virtual action_result hypothesis_pre_activation(hypothesis_idx) override {
        return action_result::new_branch();
    }

    virtual action_result hypothesis_post_activation(hypothesis_idx) override {
        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        if (curr_state().get_proof_depth() < m_max_depth) {
            Try(intros_action());
            Try(activate_hypothesis());
            Try(rec_action(m_selector));
        }
        /* The recursor tactic does very little, so we deactivate all hypotheses
           and allow m_S to process them again. */
        curr_state().deactivate_all();
        if (optional<expr> pf = m_S()) {
            return action_result::solved(*pf);
        }
        return action_result::failed();
    }

public:
    rec_strategy_fn(strategy const & S, rec_candidate_selector const & sel, unsigned max_rounds):
        m_S(S), m_selector(sel), m_init_depth(curr_state().get_proof_depth()),
        // TODO(Leo): add option: max number of steps
        m_max_depth(m_init_depth + max_rounds) {}
};

strategy rec_and_then(strategy const & S, rec_candidate_selector const & selector) {
    return [=]() { // NOLINT
        state s = curr_state();
        unsigned max_rounds = get_blast_recursion_max_rounds(ios().get_options());
        for (unsigned i = 0; i <= max_rounds; i++) {
            lean_trace_search(tout() << "starting recursor strategy with max #" << i << " round(s)\n";);
            curr_state() = s;
            if (auto pr = rec_strategy_fn(S, selector, i)())
                return pr;
        }
        return none_expr();
    };
}

static void default_selector(hypothesis_idx_buffer & r) {
    // TODO(Leo): add options to control selection
    state & s = curr_state();
    bool classes     = get_blast_recursion_class(ios().get_options());
    bool structures  = get_blast_recursion_structure(ios().get_options());
    s.for_each_hypothesis([&](hypothesis_idx hidx, hypothesis const & h) {
            expr const & type = h.get_type();
            if (!is_app(type) && !is_constant(type))
                return;
            if (!h.is_assumption() && !is_prop(type))
                return;
            if (is_relation_app(type))
                return; // we don't apply recursors to equivalence relations: =, ~, <->, etc.
            if (!classes && get_type_context().is_class(type))
                return; // ignore type classes
            expr const & I    = get_app_fn(type);
            if (!is_constant(I))
                return;
            name const & I_name = const_name(I);
            if (inductive::is_inductive_decl(env(), I_name) && (structures || *inductive::get_num_intro_rules(env(), I_name) > 1)) {
                // builtin recursive datatype with more than one constructor
                r.push_back(hidx);
                return;
            }
            list<name> Rs = get_recursors_for(env(), I_name);
            if (Rs) {
                // has user defined recursor
                r.push_back(hidx);
                return;
            }
        });
    s.sort_hypotheses(r);
}

strategy rec_and_then(strategy const & S) {
    return rec_and_then(S, default_selector);
}
}}

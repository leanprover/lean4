/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/blast/blast.h"
#include "library/blast/action_result.h"
#include "library/blast/unit/unit_actions.h"
#include "library/blast/proof_expr.h"
#include "library/blast/choice_point.h"
#include "library/blast/hypothesis.h"
#include "library/blast/util.h"
#include "library/expr_lt.h"
#include "util/rb_multi_map.h"

namespace lean {
namespace blast {

bool is_lemma(expr const & _type) {
    expr type = _type;
    bool has_antecedent = false;
    if (!is_prop(type)) return false;
    while (is_pi(type) && closed(binding_body(type))) {
        has_antecedent = true;
        type = binding_body(type);
    }
    if (has_antecedent) return true;
    else if (is_or(type)) return true;
    else return false;
}

bool is_fact(expr const & type) {
    return !is_lemma(type);
}

expr flip(expr const & e) {
    expr not_e;
    if (!blast::is_not(e, not_e)) not_e = get_app_builder().mk_not(e);
    return not_e;
}

bool is_not(expr const & e) {
    expr not_e;
    return blast::is_not(e, not_e);
}

static unsigned g_ext_id = 0;
struct unit_branch_extension : public branch_extension {
    /* We map each lemma to the two facts that it is watching. */
    rb_multi_map<hypothesis_idx, expr, unsigned_cmp> m_lemmas_to_facts;

    /* We map each fact back to the lemma hypotheses that are watching it. */
    rb_multi_map<expr, hypothesis_idx, expr_quick_cmp> m_facts_to_lemmas;

    /* We map each fact expression to its hypothesis. */
    rb_map<expr, hypothesis_idx, expr_quick_cmp>       m_facts;

    unit_branch_extension() {}
    unit_branch_extension(unit_branch_extension const & b):
        m_lemmas_to_facts(b.m_lemmas_to_facts),
        m_facts_to_lemmas(b.m_facts_to_lemmas),
        m_facts(b.m_facts) {}
    virtual ~unit_branch_extension() {}
    virtual branch_extension * clone() override { return new unit_branch_extension(*this); }
    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx hidx) override {
        if (is_fact(h.get_type())) m_facts.insert(h.get_type(), hidx);
    }
    virtual void hypothesis_deleted(hypothesis const & h, hypothesis_idx hidx) override {
        if (is_lemma(h.get_type())) {
            list<expr> const * facts = find_facts_watching_lemma(hidx);
            if (facts) {
                for_each(*facts, [&](expr const & fact) {
                        unwatch(hidx, fact);
                    });
            }
        } else if (is_fact(h.get_type())) {
            m_facts.erase(h.get_type());
            lean_assert(!find_lemmas_watching_fact(h.get_type()));
        }
    }

public:
    list<hypothesis_idx> const * find_lemmas_watching_fact(expr const & fact_type) {
        return m_facts_to_lemmas.find(fact_type);
    }
    list<expr> const * find_facts_watching_lemma(hypothesis_idx lemma_hidx) {
        return m_lemmas_to_facts.find(lemma_hidx);
    }
    void unwatch(hypothesis_idx lemma_hidx, expr const & fact_type) {
        m_lemmas_to_facts.filter(lemma_hidx, [&](expr const & fact_type2) {
                return fact_type != fact_type2;
            });
        m_facts_to_lemmas.erase(fact_type, lemma_hidx);
    }
    hypothesis_idx const * find_fact(expr const & fact_type) {
        return m_facts.find(fact_type);
    }
    void watch(hypothesis_idx lemma_hidx, expr const & fact_type) {
        m_lemmas_to_facts.insert(lemma_hidx, fact_type);
        m_facts_to_lemmas.insert(fact_type, lemma_hidx);
    }
};

void initialize_unit_propagate() {
    g_ext_id = register_branch_extension(new unit_branch_extension());
}

void finalize_unit_propagate() { }

static unit_branch_extension & get_extension() {
    return static_cast<unit_branch_extension&>(curr_state().get_extension(g_ext_id));
}

/* Recall the general form of the lemmas we handle in this module:
   A_1 -> ... -> A_n -> B_1 \/ (B2 \/ ... \/ B_m)...)

   There are three different scenarios in which we propagate:
   (1) We have all of the A_i, and the negations of all but the last B_j.
   (2) We are missing an A_i.
   (3) We are missing a B_j.

   The first thing we do is check whether or not we are able to propagate.
   If so, we start instantiating the A_i. If we hit a missing literal,
   we store the proof so far, create a local for the consequent, prove false,
   and then conclude with [lemma imp_right : (A → B) → ¬ B → ¬ A].

   If we instantiate all the A_i, we start using [lemma or_resolve_left : A ∨ B → ¬ A → B]
   to cross of the B_j. If we have all but the last one, we simply return the resulting proof.

   If we are missing a B_j, we store the proof so far, create a local for the right-hand-side of
   the disjunct, prove false, and then conclude with [lemma or_resolve_right : A ∨ B → ¬ B → A].
*/


bool can_propagate(expr const & _type, buffer<expr, 2> & to_watch) {
    lean_assert(is_lemma(_type));
    expr type = _type;
    unsigned num_watching = 0;
    unit_branch_extension & ext = get_extension();

    bool missing_non_Prop = false;
    /* Traverse the A_i */
    while (is_pi(type) && closed(binding_body(type))) {
        expr arg;
        hypothesis_idx const * fact_hidx = ext.find_fact(binding_domain(type));
        if (!fact_hidx) {
            /* We do not support non-Prop antecedents since we cannot negate them */
            if (!is_prop(binding_domain(type))) missing_non_Prop = true;
            to_watch.push_back(binding_domain(type));
            num_watching++;
            if (num_watching == 2) return false;
        }
        type = binding_body(type);
    }

    /* Traverse the B_j */
    expr lhs, rhs;
    while (is_or(type, lhs, rhs)) {
        hypothesis_idx const * fact_hidx = ext.find_fact(flip(lhs));
        if (!fact_hidx) {
            to_watch.push_back(flip(lhs));
            num_watching++;
            if (num_watching == 2) return false;
        }
        type = rhs;
    }

    hypothesis_idx const * fact_hidx = ext.find_fact(flip(type));
    if (!fact_hidx) {
        to_watch.push_back(flip(type));
        num_watching++;
        if (num_watching == 2) return false;
    }
    return !missing_non_Prop;
}

action_result unit_lemma(hypothesis_idx hidx, expr const & _type, expr const & _proof) {
    lean_assert(is_lemma(_type));
    unit_branch_extension & ext = get_extension();

    /* (1) Find the facts that are watching this lemma and clear them. */
    list<expr> const * watching = ext.find_facts_watching_lemma(hidx);
    if (watching) {
        lean_assert(length(*watching) == 2);
        for_each(*watching, [&](expr const & fact) { ext.unwatch(hidx, fact); });
    }

    /* (2) Check if we can propagate */
    buffer<expr, 2> to_watch;
    if (!can_propagate(_type, to_watch)) {
        for (expr const & e : to_watch) ext.watch(hidx, e);
        return action_result::failed();
    }

    expr type = _type;
    expr proof = _proof;
    expr final_type;
    expr proof_left;
    expr proof_init_right;
    expr type_init_right;
    bool missing_A = false;
    bool missing_B = false;

    /* (3) Traverse the binding domains */
    while (is_pi(type) && closed(binding_body(type))) {
        hypothesis_idx const * fact_hidx = ext.find_fact(binding_domain(type));
        if (fact_hidx) {
            proof = mk_app(proof, curr_state().get_hypothesis_decl(*fact_hidx).get_self());
        } else {
            lean_assert(!missing_A);
            missing_A = true;
            final_type = get_app_builder().mk_not(binding_domain(type));
            proof_left = proof;
            type_init_right = binding_body(type);
            proof_init_right = mk_fresh_local(type_init_right);
            proof = proof_init_right;
        }
        type = binding_body(type);
    }

    /* (4) Traverse the conclusion */
    expr lhs, rhs;
    while (is_or(type, lhs, rhs)) {
        hypothesis_idx const * fact_hidx = ext.find_fact(flip(lhs));
        if (fact_hidx) {
            expr arg = curr_state().get_hypothesis_decl(*fact_hidx).get_self();
            if (is_not(lhs)) {
                proof = get_app_builder().mk_app(get_or_neg_resolve_left_name(),
                                                 proof, arg);
            } else {
                proof = get_app_builder().mk_app(get_or_resolve_left_name(),
                                                 proof, arg);
            }
        } else {
            lean_assert(!missing_A);
            lean_assert(!missing_B);
            missing_B = true;
            final_type = lhs;
            proof_left = proof;
            type_init_right = rhs;
            proof_init_right = mk_fresh_local(type_init_right);
            proof = proof_init_right;
        }
        type = rhs;
    }

    expr final_proof;
    if (missing_A || missing_B) {
        hypothesis_idx const * fact_hidx = ext.find_fact(flip(type));
        lean_assert(fact_hidx);
        expr arg = curr_state().get_hypothesis_decl(*fact_hidx).get_self();
        if (is_not(type)) proof = mk_app(proof, arg);
        else proof = mk_app(arg, proof);
        expr proof_right = get_app_builder().mk_app(get_not_wrap_name(), type_init_right, Fun(proof_init_right, proof));
        if (missing_A) {
            final_proof = get_app_builder().mk_app(get_implies_resolve_name(), proof_left, proof_right);
        } else {
            final_proof = get_app_builder().mk_app(get_or_resolve_right_name(), proof_left, proof_right);
        }
    } else {
        final_type = type;
        final_proof = proof;
    }

    curr_state().mk_hypothesis(final_type, final_proof);
    return action_result::new_branch();
}

action_result unit_fact(expr const & type) {
    unit_branch_extension & ext = get_extension();
    list<hypothesis_idx> const * lemmas = ext.find_lemmas_watching_fact(type);
    if (!lemmas) return action_result::failed();
    bool success = false;
    for_each(*lemmas, [&](hypothesis_idx const & hidx) {
            hypothesis const & h = curr_state().get_hypothesis_decl(hidx);
            action_result r = unit_lemma(hidx, whnf(h.get_type()), h.get_self());
            success = success || (r.get_kind() == action_result::NewBranch);
        });
    if (success) return action_result::new_branch();
    else return action_result::failed();
}

action_result unit_propagate(unsigned hidx) {
    hypothesis const & h = curr_state().get_hypothesis_decl(hidx);
    expr type = whnf(h.get_type());
    if (is_lemma(type)) return unit_lemma(hidx, type, h.get_self());
    else if (is_fact(type)) return unit_fact(type);
    else return action_result::failed();
}
}}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"
#include "library/blast/choice_point.h"
#include "library/blast/gexpr.h"

namespace lean {
namespace blast {
struct backward_proof_step_cell : public proof_step_cell {
    branch     m_branch;
    expr       m_proof;
    list<expr> m_mvars;
    backward_proof_step_cell(branch const & b, expr const & pr, list<expr> const & mvars):
        m_branch(b), m_proof(pr), m_mvars(mvars) {
        lean_assert(!empty(m_mvars));
    }

    virtual ~backward_proof_step_cell() {}

    virtual action_result resolve(expr const & pr) const override {
        state & s = curr_state();
        s.set_branch(m_branch);
        expr mvar = head(m_mvars);
        if (!is_def_eq(mvar, pr))
            return action_result::failed();
        list<expr> new_mvars = tail(m_mvars);
        if (empty(new_mvars)) {
            // solved all branches
            expr r = to_proof_expr(s.instantiate_urefs_mrefs(m_proof));
            r      = unfold_hypotheses_ge(s, r);
            return action_result::solved(r);
        } else {
            s.pop_proof_step();
            auto bcell = new backward_proof_step_cell(m_branch, m_proof, new_mvars);
            s.push_proof_step(bcell);
            expr new_target = s.instantiate_urefs_mrefs(infer_type(head(new_mvars)));
            s.set_target(new_target);
            return action_result::new_branch();
        }
    }
};

static action_result try_lemma(gexpr const & e, bool prop_only_branches) {
    state & s = curr_state();
    expr f    = e.to_expr();
    expr type = infer_type(f);
    expr pr   = f;
    buffer<expr> mvars;
    while (true) {
        type = whnf(type);
        if (!is_pi(type))
            break;
        expr mvar = s.mk_metavar(binding_domain(type));
        mvars.push_back(mvar);
        pr        = mk_app(pr, mvar);
        type      = instantiate(binding_body(type), mvar);
    }
    expr target = s.get_target();
    if (!is_def_eq(target, type))
        return action_result::failed();
    bool has_unassigned = false;
    buffer<expr> branches;
    unsigned i = mvars.size();
    while (i > 0) {
        --i;
        if (!s.is_mref_assigned(mvars[i])) {
            has_unassigned = true;
            if (!prop_only_branches || is_prop(infer_type(mvars[i]))) {
                branches.push_back(mvars[i]);
            }
        }
    }
    if (!has_unassigned) {
        // all meta-variables have been assigned
        return action_result::solved(to_proof_expr(s.instantiate_urefs_mrefs(pr)));
    }
    if (branches.empty()) {
        // some meta-variables were not assigned, but they are not propositions,
        // and since prop_only_branches == true, we only create branches for propositions
        return action_result::failed();
    }
    auto bcell = new backward_proof_step_cell(s.get_branch(), pr, to_list(branches));
    s.push_proof_step(bcell);
    expr new_target = s.instantiate_urefs_mrefs(infer_type(branches[0]));
    s.set_target(new_target);
    return action_result::new_branch();
}

class backward_choice_point_cell : public choice_point_cell {
    state       m_state;
    list<gexpr> m_lemmas;
    bool        m_prop_only;
public:
    backward_choice_point_cell(state const & s, list<gexpr> const & lemmas, bool prop_only):
        m_state(s), m_lemmas(lemmas), m_prop_only(prop_only) {}

    virtual action_result next() {
        while (!empty(m_lemmas)) {
            curr_state()    = m_state;
            gexpr lemma     = head(m_lemmas);
            m_lemmas        = tail(m_lemmas);
            action_result r = try_lemma(lemma, m_prop_only);
            if (!failed(r))
                return r;
        }
        return action_result::failed();
    }
};

action_result backward_action(list<gexpr> const & lemmas, bool prop_only_branches) {
    state  s = curr_state();
    auto it  = lemmas;
    while (!empty(it)) {
        action_result r = try_lemma(head(it), prop_only_branches);
        it              = tail(it);
        if (!failed(r)) {
            // create choice point
            if (!empty(it))
                push_choice_point(choice_point(new backward_choice_point_cell(s, it, prop_only_branches)));
            return r;
        }
        curr_state() = s;
    }
    return action_result::failed();
}

action_result constructor_action(bool prop_only_branches) {
    state s = curr_state();
    expr I  = get_app_fn(s.get_target());
    if (!is_constant(I) || !inductive::is_inductive_decl(env(), const_name(I)))
        return action_result::failed();
    buffer<name> c_names;
    get_intro_rule_names(env(), const_name(I), c_names);
    buffer<gexpr> lemmas;
    for (name c_name : c_names)
        lemmas.push_back(gexpr(c_name));
    return backward_action(to_list(lemmas), prop_only_branches);
}
}}

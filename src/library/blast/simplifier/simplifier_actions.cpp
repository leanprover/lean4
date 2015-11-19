/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/blast/simple_actions.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/simplifier/simplifier.h"

namespace lean {
namespace blast {
static unsigned g_ext_id = 0;
struct simplifier_branch_extension : public branch_extension {
    simp_rule_sets m_srss;
    simplifier_branch_extension() {}
    simplifier_branch_extension(simplifier_branch_extension const & b):
        m_srss(b.m_srss) {}
    virtual ~simplifier_branch_extension() {}
    virtual branch_extension * clone() override { return new simplifier_branch_extension(*this); }
    virtual void initialized() override { m_srss = ::lean::get_simp_rule_sets(env()); }
    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx hidx) override { }
    virtual void hypothesis_deleted(hypothesis const & h, hypothesis_idx) override { }
    simp_rule_sets const & get_simp_rule_sets() const { return m_srss; }
};

void initialize_simplifier_actions() {
    g_ext_id = register_branch_extension(new simplifier_branch_extension());
}

void finalize_simplifier_actions() {
}

static simplifier_branch_extension & get_extension() {
    return static_cast<simplifier_branch_extension&>(curr_state().get_extension(g_ext_id));
}

static bool use_iff(expr const & target) {
    return is_standard(env()) && is_prop(target);
}

class simplify_target_proof_step_cell : public proof_step_cell {
    bool m_iff;
    expr m_eq_pr;
public:
    simplify_target_proof_step_cell(bool iff, expr const & eq_pr):
        m_iff(iff), m_eq_pr(eq_pr) {}

    virtual ~simplify_target_proof_step_cell() {}

    virtual action_result resolve(expr const & pr) const override {
        try {
            app_builder & b = get_app_builder();
            if (m_iff)
                return action_result::solved(b.mk_app(get_iff_mpr_name(), m_eq_pr, pr));
            else
                return action_result::solved(b.mk_app(get_eq_mpr_name(), m_eq_pr, pr));
        } catch (app_builder_exception &) {
            return action_result::failed();
        }
    }
};

action_result simplify_target_action() {
    state & s   = curr_state();
    expr target = s.get_target();
    bool iff    = use_iff(target);
    name rname  = iff ? get_iff_name() : get_eq_name();
    auto r = simplify(rname, target, get_extension().get_simp_rule_sets());
    if (!r.has_proof())
        return action_result::failed(); // did nothing
    s.push_proof_step(new simplify_target_proof_step_cell(iff, r.get_proof()));
    s.set_target(r.get_new());
    trace_action("simplify");
    return action_result::new_branch();
}
}}

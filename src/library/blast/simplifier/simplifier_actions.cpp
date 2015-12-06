/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"
#include "library/blast/options.h"
#include "library/blast/simplifier/simplifier.h"
#include "library/blast/simplifier/ceqv.h"

namespace lean {
namespace blast {
static unsigned g_ext_id = 0;
struct simplifier_branch_extension : public branch_extension {
    simp_rule_sets m_srss;
    bool           m_simp_target{false}; // true if target needs to be simplified again
    simplifier_branch_extension() {}
    simplifier_branch_extension(simplifier_branch_extension const & b):
        m_srss(b.m_srss) {}
    virtual ~simplifier_branch_extension() {}
    virtual branch_extension * clone() override { return new simplifier_branch_extension(*this); }
    virtual void initialized() override { m_srss = ::lean::get_simp_rule_sets(env()); }
    virtual void target_updated() override { m_simp_target = true; }
    virtual void hypothesis_activated(hypothesis const &, hypothesis_idx) override { }
    virtual void hypothesis_deleted(hypothesis const &, hypothesis_idx) override { }
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
    if (!get_config().m_simp)
        return action_result::failed();
    auto & ext  = get_extension();
    if (!ext.m_simp_target)
        return action_result::failed(); // nothing to be done
    ext.m_simp_target = false;
    state & s         = curr_state();
    expr target       = s.get_target();
    bool iff          = use_iff(target);
    name rname        = iff ? get_iff_name() : get_eq_name();
    auto r = simplify(rname, target, ext.get_simp_rule_sets());
    if (r.get_new() == target)
        return action_result::failed(); // did nothing
    if (r.has_proof()) {
        // Remark: we only need to create the proof step if a proof was generated.
        // If a proof was not generated and the resulting expression is not
        // structurally equal, then they are definitionally equal and no proof is
        // needed
        s.push_proof_step(new simplify_target_proof_step_cell(iff, r.get_proof()));
    }
    s.set_target(r.get_new());
    trace_action("simplify");
    return action_result::new_branch();
}

action_result simplify_hypothesis_action(hypothesis_idx hidx) {
    if (!get_config().m_simp)
        return action_result::failed();
    state & s            = curr_state();
    if (s.has_target_forward_deps(hidx)) {
        // We currently do not try to simplify a hypothesis if other
        // hypotheses or target depends on it.
        return action_result::failed();
    }
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    if (!is_prop(h.get_type())) {
        // We currently only simplify propositions.
        return action_result::failed();
    }
    auto & ext           = get_extension();
    auto r = simplify(get_iff_name(), h.get_type(), ext.get_simp_rule_sets());
    if (r.get_new() == h.get_type())
        return action_result::failed(); // did nothing
    expr new_h_proof;
    if (r.has_proof()) {
        new_h_proof = get_app_builder().mk_app(get_iff_mp_name(), r.get_proof(), h.get_self());
    } else {
        // they are definitionally equal
        new_h_proof = h.get_self();
    }
    s.mk_hypothesis(r.get_new(), new_h_proof);
    s.del_hypothesis(hidx);
    return action_result::new_branch();
}

action_result add_simp_rule_action(hypothesis_idx hidx) {
    if (!get_config().m_simp)
        return action_result::failed();
    blast_tmp_type_context ctx;
    state & s            = curr_state();
    hypothesis const & h = s.get_hypothesis_decl(hidx);
    list<expr_pair> ps   = to_ceqvs(*ctx, h.get_type(), h.get_self());
    if (!ps)
        return action_result::failed();
    auto & ext           = get_extension();
    bool added           = false;
    for (auto const & p : ps) {
        try {
            ext.m_srss = add(*ctx, ext.m_srss, h.get_name(), p.first, p.second, LEAN_SIMP_DEFAULT_PRIORITY);
            added      = true;
        } catch (exception &) {
            // TODO(Leo, Daniel): store event
        }
    }
    return added ? action_result::new_branch() : action_result::failed();
}
}}

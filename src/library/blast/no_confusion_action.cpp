/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/inductive/inductive.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"

namespace lean {
namespace blast {
struct no_confusion_proof_step_cell : public proof_step_cell {
    name m_I_name;
    expr m_target;
    expr m_eq_href;
    unsigned m_num_new_eqs;
    no_confusion_proof_step_cell(name const & I_name, expr const & t, expr const & e, unsigned n):
        m_I_name(I_name), m_target(t), m_eq_href(e), m_num_new_eqs(n) {}
    virtual ~no_confusion_proof_step_cell() {}

    virtual action_result resolve(expr const & pr) const override {
        try {
            expr it   = pr;
            bool skip = true;
            for (unsigned i = 0; i < m_num_new_eqs; i++) {
                if (!is_lambda(it)) {
                    break;
                    skip = false;
                }
                it = binding_body(it);
            }
            if (skip && closed(it)) {
                // new eq hypotheses were not used
                return action_result::solved(it);
            }
            state & s = curr_state();
            app_builder & b = get_app_builder();
            hypothesis const * h = s.get_hypothesis_decl(href_index(m_eq_href));
            lean_assert(h);
            expr type = h->get_type();
            expr lhs, rhs;
            lean_verify(is_eq(type, lhs, rhs));
            name nc_name(m_I_name, "no_confusion");
            expr new_pr = mk_app(b.mk_app(nc_name, {m_target, lhs, rhs, m_eq_href}), pr);
            return action_result::solved(new_pr);
        } catch (app_builder_exception &) {
            return action_result::failed();
        }
    }
};

action_result no_confusion_action(hypothesis_idx hidx) {
    try {
        state & s       = curr_state();
        app_builder & b = get_app_builder();
        hypothesis const * h = s.get_hypothesis_decl(hidx);
        lean_assert(h);
        expr type = h->get_type();
        expr lhs, rhs;
        if (!is_eq(type, lhs, rhs))
            return action_result::failed();
        lhs = whnf(lhs);
        rhs = whnf(rhs);
        optional<name> c1 = is_constructor_app(env(), lhs);
        optional<name> c2 = is_constructor_app(env(), rhs);
        if (!c1 || !c2)
            return action_result::failed();
        expr A = whnf(infer_type(lhs));
        expr I = get_app_fn(A);
        if (!is_constant(I) || !inductive::is_inductive_decl(env(), const_name(I)))
            return action_result::failed();
        name nct_name(const_name(I), "no_confusion_type");
        if (!env().find(nct_name))
            return action_result::failed();
        expr target  = s.get_target();
        expr nct     = whnf(b.mk_app(nct_name, target, lhs, rhs));
        if (c1 == c2) {
            if (!is_pi(nct))
                return action_result::failed();
            if (s.has_target_forward_deps(hidx)) {
                // TODO(Leo): we currently do not handle this case.
                // To avoid non-termination we remove the given hypothesis, if there
                // forward dependencies, we would also have to remove them.
                // Remark: this is a low priority refinement since it will not happen
                // very often in practice.
                return action_result::failed();
            }
            unsigned num_params  = *inductive::get_num_params(env(), const_name(I));
            unsigned cnstr_arity = get_arity(env().get(*c1).get_type());
            lean_assert(cnstr_arity >= num_params);
            unsigned num_new_eqs = cnstr_arity - num_params;
            s.push_proof_step(new no_confusion_proof_step_cell(const_name(I), target, h->get_self(), num_new_eqs));
            s.set_target(binding_domain(nct));
            s.del_hypothesis(hidx);
            trace_action("no_confusion");
            return action_result::new_branch();
        } else {
            name nc_name(const_name(I), "no_confusion");
            expr pr = b.mk_app(nc_name, {target, lhs, rhs, h->get_self()});
            trace_action("no_confusion");
            return action_result::solved(pr);
        }
    } catch (app_builder_exception &) {
        return action_result::failed();
    }
}
}}

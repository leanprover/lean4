/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/blast/revert.h"
#include "library/blast/intros_action.h"
#include "library/blast/blast.h"
#include "library/blast/trace.h"

namespace lean {
namespace blast {
struct subst_proof_step_cell : public proof_step_cell {
    expr  m_target;
    expr  m_eq_href;
    expr  m_rhs;
    bool  m_dep;
    subst_proof_step_cell(expr const & t, expr const & e, expr const & r, bool d):
        m_target(t), m_eq_href(e), m_rhs(r), m_dep(d) {}
    virtual ~subst_proof_step_cell() {}

    virtual action_result resolve(expr const & pr) const override {
        try {
            state & s = curr_state();
            app_builder & b = get_app_builder();
            if (m_dep) {
                buffer<expr> hs;
                hs.push_back(m_rhs);
                hs.push_back(m_eq_href);
                expr motive = s.mk_lambda(hs, m_target);
                return action_result::solved(b.mk_eq_drec(motive, pr, m_eq_href));
            } else {
                expr motive = s.mk_lambda(m_rhs, m_target);
                return action_result::solved(b.mk_eq_rec(motive, pr, m_eq_href));
            }
        } catch (app_builder &) {
            return action_result::failed();
        }
    }
};

bool subst_core(hypothesis_idx hidx) {
    state & s       = curr_state();
    state saved     = s;
    app_builder & b = get_app_builder();
    hypothesis const * h = s.get_hypothesis_decl(hidx);
    lean_assert(h);
    expr type = h->get_type();
    expr lhs, rhs;
    lean_verify(is_eq(type, lhs, rhs));
    lean_assert(is_href(rhs));
    try {
        hypothesis_idx_buffer_set to_revert;
        s.collect_direct_forward_deps(href_index(rhs),
                                      to_revert,
                                      [&](hypothesis_idx d) { return d != hidx; });
        s.collect_direct_forward_deps(hidx, to_revert);
        unsigned num = revert(to_revert);
        expr target  = s.get_target();
        expr new_target = abstract(target, h->get_self());
        bool dep        = !closed(new_target);
        bool skip       = to_revert.empty();
        if (dep) {
            skip       = false;
            new_target = instantiate(new_target, b.mk_eq_refl(lhs));
        }
        new_target = abstract(new_target, rhs);
        if (!closed(new_target))
            skip       = false;
        if (!skip) {
            new_target = instantiate(new_target, lhs);
            s.push_proof_step(new subst_proof_step_cell(target, h->get_self(), rhs, dep));
            s.set_target(new_target);
            lean_verify(intros_action(num));
        }
        lean_verify(s.del_hypothesis(hidx));
        lean_verify(s.del_hypothesis(href_index(rhs)));
        trace_action("subst");
        return true;
    } catch (app_builder_exception &) {
        s = saved;
        return false;
    }
}

action_result subst_action(hypothesis_idx hidx) {
    state & s       = curr_state();
    app_builder & b = get_app_builder();
    hypothesis const * h = s.get_hypothesis_decl(hidx);
    lean_assert(h);
    expr type = h->get_type();
    expr lhs, rhs;
    if (!is_eq(type, lhs, rhs))
        return action_result::failed();
    if (is_href(rhs)) {
        return action_result(subst_core(hidx));
    } else if (is_href(lhs)) {
        if (s.has_forward_deps(href_index(lhs))) {
            // TODO(Leo): we don't handle this case yet.
            // Other hypotheses depend on this equality.
            return action_result::failed();
        }
        state saved   = s;
        try {
            expr new_eq   = b.mk_eq(rhs, lhs);
            expr new_pr   = b.mk_eq_symm(h->get_self());
            expr new_href = s.mk_hypothesis(new_eq, new_pr);
            if (subst_core(href_index(new_href))) {
                return action_result::new_branch();
            } else {
                s = saved;
                return action_result::failed();
            }
        } catch (app_builder_exception &) {
            s = saved;
            return action_result::failed();
        }
    } else {
        return action_result::failed();
    }
}
}}

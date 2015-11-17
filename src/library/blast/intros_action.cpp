/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/blast/blast.h"
#include "library/blast/proof_expr.h"

namespace lean {
namespace blast {
struct intros_proof_step_cell : public proof_step_cell {
    list<expr> m_new_hs;
    virtual ~intros_proof_step_cell() {}
    virtual action_result resolve(expr const & pr) const override {
        expr new_pr = mk_proof_lambda(curr_state(), m_new_hs, pr);
        return action_result::solved(new_pr);
    }

    virtual bool is_silent() const override { return true; }
};

bool intros_action(unsigned max) {
    if (max == 0)
        return true;
    state &  s  = curr_state();
    expr target = whnf(s.get_target());
    if (!is_pi(target))
        return false;
    auto pcell = new intros_proof_step_cell();
    s.push_proof_step(pcell);
    buffer<expr> new_hs;
    for (unsigned i = 0; i < max; i++) {
        if (!is_pi(target))
            break;
        expr href;
        expr htype = head_beta_reduce(binding_domain(target));
        if (is_default_var_name(binding_name(target)) && closed(binding_body(target))) {
            href  = s.mk_hypothesis(htype);
        } else {
            href  = s.mk_hypothesis(binding_name(target), htype);
        }
        new_hs.push_back(href);
        target     = whnf(instantiate(binding_body(target), href));
    }
    pcell->m_new_hs = to_list(new_hs);
    s.set_target(target);
    return true;
}

bool intros_action() {
    return intros_action(std::numeric_limits<unsigned>::max());
}
}}

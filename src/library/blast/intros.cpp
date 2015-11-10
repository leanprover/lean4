/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
class intros_proof_step_cell : public proof_step_cell {
    list<expr> m_new_hs;
public:
    intros_proof_step_cell(list<expr> const & new_hs):
        m_new_hs(new_hs) {}
    virtual ~intros_proof_step_cell() {}

    virtual optional<expr> resolve(state & s, expr const & pr) const {
        expr new_pr = s.mk_lambda(m_new_hs, pr);
        return some_expr(new_pr);
    }
};

bool intros_action() {
    state &  s  = curr_state();
    expr target = whnf(s.get_target());
    if (!is_pi(target))
        return false;
    buffer<expr> new_hs;
    while (is_pi(target)) {
        expr href  = s.mk_hypothesis(binding_name(target), binding_domain(target));
        new_hs.push_back(href);
        target     = whnf(instantiate(binding_body(target), href));
    }
    s.push_proof_step(proof_step(new intros_proof_step_cell(to_list(new_hs))));
    s.set_target(target);
    return true;
}
}}

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
    list<expr> m_new_locals;
public:
    intros_proof_step_cell(list<expr> const & new_hs, list<expr> const & new_locals):
        m_new_hs(new_hs), m_new_locals(new_locals) {}
    virtual ~intros_proof_step_cell() {}

    virtual optional<expr> resolve(state & s, expr const & pr) {
        buffer<expr> locals;
        to_buffer(m_new_locals, locals);
        expr new_pr = Fun(locals, s.expand_hrefs(pr, m_new_hs));
        return some_expr(new_pr);
    }
};

bool intros_action() {
    state &  s  = curr_state();
    expr target = whnf(s.get_target());
    if (!is_pi(target))
        return false;
    buffer<expr> new_hs;
    buffer<expr> new_locals;
    while (is_pi(target)) {
        expr local = mk_fresh_local(binding_domain(target));
        expr href  = s.add_hypothesis(binding_name(target), binding_domain(target), local);
        new_hs.push_back(href);
        new_locals.push_back(local);
        target     = whnf(instantiate(binding_body(target), href));
    }
    s.push_proof_step(proof_step(new intros_proof_step_cell(to_list(new_hs), to_list(new_locals))));
    s.set_target(target);
    return true;
}
}}

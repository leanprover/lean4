/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/revert_action.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
struct revert_proof_step_cell : public proof_step_cell {
    list<expr> m_hs;
    revert_proof_step_cell(list<expr> const & hs):m_hs(hs) {}

    virtual ~revert_proof_step_cell() {}

    virtual action_result resolve(expr const & pr) const override {
        expr new_pr = mk_app(pr, m_hs);
        return action_result::solved(new_pr);
    }

    virtual bool is_silent() const override { return true; }
};

unsigned revert_action(hypothesis_idx_buffer_set & hidxs) {
    state & s = curr_state();
    unsigned hidxs_size = hidxs.as_buffer().size();
    for (unsigned i = 0; i < hidxs_size; i++) {
        s.collect_forward_deps(hidxs.as_buffer()[i], hidxs);
    }
    s.sort_hypotheses(hidxs);
    buffer<expr> hs;
    s.to_hrefs(hidxs.as_buffer(), hs);
    expr target     = s.get_target();
    expr new_target = s.mk_pi(hs, target);
    s.set_target(new_target);
    s.push_proof_step(new revert_proof_step_cell(to_list(hs)));
    lean_verify(s.del_hypotheses(hidxs.as_buffer()));
    return hidxs.as_buffer().size();
}

unsigned revert_action(buffer<hypothesis_idx> & hidxs) {
    hypothesis_idx_buffer_set _hidxs(hidxs);
    return revert_action(_hidxs);
}
}}

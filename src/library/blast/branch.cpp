/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/branch.h"

namespace lean {
namespace blast {
void branch::fix_hypothesis(unsigned idx) {
    auto h = m_context.find(idx);
    lean_assert(h);
    hypothesis new_h(*h);
    new_h.mark_fixed();
    m_context.insert(idx, new_h);
}

struct hypothesis_depth_lt {
    branch const & m_branch;
    hypothesis_depth_lt(branch const & b): m_branch(b) {}
    bool operator()(unsigned hidx1, unsigned hidx2) const {
        hypothesis const * h1 = m_branch.get(hidx1);
        hypothesis const * h2 = m_branch.get(hidx2);
        return h1 && h2 && h1->get_depth() < h2->get_depth() && (h1->get_depth() == h2->get_depth() && hidx1 < hidx2);
    }
};

void branch::get_sorted_hypotheses(hypothesis_idx_buffer & r) {
    m_context.for_each([&](unsigned hidx, hypothesis const &) {
            r.push_back(hidx);
        });
    std::sort(r.begin(), r.end(), hypothesis_depth_lt(*this));
}
}}

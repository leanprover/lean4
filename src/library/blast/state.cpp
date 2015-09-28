/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/for_each_fn.h"
#include "library/blast/state.h"

namespace lean {
namespace blast {
state::state():m_next_mref_index(0) {}

expr state::mk_metavar(hypothesis_idx_buffer const & ctx, expr const & type) {
    hypothesis_idx_set  ctx_as_set;
    for (unsigned const & hidx : ctx)
        ctx_as_set.insert(hidx);
    for_each(type, [&](expr const & e, unsigned) {
            if (!has_lref(e))
                return false;
            if (is_lref(e)) {
                lean_assert(ctx_as_set.contains(lref_index(e)));
                m_main.fix_hypothesis(e);
                return false;
            }
            return true; // continue search
        });
    unsigned idx = m_next_mref_index;
    m_next_mref_index++;
    m_metavar_decls.insert(idx, metavar_decl(to_list(ctx), ctx_as_set, type));
    return blast::mk_mref(idx);
}

expr state::mk_metavar(expr const & type) {
    hypothesis_idx_buffer ctx;
    m_main.get_sorted_hypotheses(ctx);
    return mk_metavar(ctx, type);
}
}}

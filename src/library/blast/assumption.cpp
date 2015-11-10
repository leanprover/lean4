/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/blast.h"

namespace lean {
namespace blast {
optional<expr> assumption_action() {
    // TODO(Leo): this is a very naive implementation that just traverses the set of
    // active hypothesis
    state const & s     = curr_state();
    expr const & target = s.get_target();
    auto hidx = s.find_active_hypothesis([&](unsigned, hypothesis const & h) {
            return is_def_eq(h.get_type(), target);
        });
    if (!hidx)
        return none_expr();
    hypothesis const * h = s.get_hypothesis_decl(*hidx);
    return some_expr(h->get_self());
}
}}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/blast/util.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {
// TODO(Leo): we should create choice points when there are meta-variables
optional<expr> assumption_action() {
    state const & s     = curr_state();
    expr const & target = s.get_target();
    for (hypothesis_idx hidx : s.get_head_related()) {
        hypothesis const * h = s.get_hypothesis_decl(hidx);
        lean_assert(h);
        if (is_def_eq(h->get_type(), target))
            return some_expr(h->get_self());
    }
    return none_expr();
}

optional<expr> assumption_contradiction_actions(hypothesis_idx hidx) {
    state const & s      = curr_state();
    app_builder & b      = get_app_builder();
    hypothesis const * h = s.get_hypothesis_decl(hidx);
    lean_assert(h);
    expr const & type    = h->get_type();
    if (blast::is_false(type)) {
        return some_expr(b.mk_false_rec(s.get_target(), h->get_self()));
    }
    if (is_def_eq(type, s.get_target())) {
        return some_expr(h->get_self());
    }
    expr p1 = type;
    bool is_neg1 = is_not(type, p1);
    for (hypothesis_idx hidx2 : s.get_head_related(hidx)) {
        hypothesis const * h2 = s.get_hypothesis_decl(hidx2);
        expr type2 = h2->get_type();
        expr p2    = type2;
        bool is_neg2 = is_not(type2, p2);
        if (is_neg1 != is_neg2) {
            if (is_def_eq(p1, p2)) {
                if (is_neg1) {
                    return some_expr(b.mk_app(get_absurd_name(), {s.get_target(), h2->get_self(), h->get_self()}));
                } else {
                    lean_assert(is_neg2);
                    return some_expr(b.mk_app(get_absurd_name(), {s.get_target(), h->get_self(), h2->get_self()}));
                }
            }
        }
    }
    return none_expr();
}
}}

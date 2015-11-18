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

/* Close branch IF h is of the form (H : a ~ a) where ~ is a reflexive relation */
static optional<expr> try_not_refl_relation(hypothesis const & h) {
    expr p;
    if (!is_not(h.get_type(), p))
        return none_expr();
    name rop; expr lhs, rhs;
    if (is_relation_app(p, rop, lhs, rhs) && is_def_eq(lhs, rhs)) {
        try {
            app_builder & b = get_app_builder();
            expr rfl = b.mk_refl(rop, lhs);
            return some_expr(b.mk_app(get_absurd_name(), curr_state().get_target(), rfl, h.get_self()));
        } catch (app_builder_exception &) {}
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
    if (auto pr = try_not_refl_relation(*h))
        return pr;
    expr p1 = type;
    bool is_neg1 = is_not(type, p1);
    /* try to find complement */
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

optional<expr> trivial_action() {
    try {
        state s = curr_state();
        expr target = s.get_target();
        /* ignore if target contains meta-variables */
        if (has_expr_metavar(target))
            return none_expr();

        /* true */
        if (target == mk_true()) {
            return some_expr(mk_true_intro());
        }

        /* a ~ a */
        name rop; expr lhs, rhs;
        if (is_relation_app(target, rop, lhs, rhs) && is_def_eq(lhs, rhs)) {
            return some_expr(get_app_builder().mk_refl(rop, lhs));
        }

        return none_expr();
    } catch (app_builder_exception &) {
        return none_expr();
    }
}

bool discard(hypothesis_idx hidx) {
    state s = curr_state();
    hypothesis const * h = s.get_hypothesis_decl(hidx);
    lean_assert(h);
    expr type            = h->get_type();
    // We only discard a hypothesis if it doesn't have dependencies.
    if (s.has_target_forward_deps(hidx))
        return false;
    // We only discard propositions
    if (!is_prop(type))
        return false;
    // 1- (H : true)
    if (is_constant(type, get_true_name()))
        return true;
    // 2- (H : a ~ a)
    name rop; expr lhs, rhs;
    if (is_relation_app(type, rop, lhs, rhs) && is_def_eq(lhs, rhs) && is_reflexive(rop))
        return true;
    // 3- We already have an equivalent hypothesis
    for (hypothesis_idx hidx2 : s.get_head_related(hidx)) {
        if (hidx == hidx2)
            continue;
        hypothesis const * h2 = s.get_hypothesis_decl(hidx2);
        expr type2 = h2->get_type();
        if (is_def_eq(type, type2))
            return true;
    }
    return false;
}
}}

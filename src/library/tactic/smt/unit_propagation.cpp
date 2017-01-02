/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/util.h"
#include "library/tactic/smt/unit_propagation.h"

namespace lean {
static bool is_lemma(type_context & ctx, expr e) {
    if (!ctx.is_prop(e)) return false;
    bool arrow = false;
    while (is_arrow(e) && !is_not(e)) {
        arrow = true;
        e     = binding_body(e);
    }
    return arrow || is_or(e);
}

/** \brief e is a dependent lemma when
    - e is a proposition
    - e is of the form (Pi (x : A), B)
    - A is a proposition
    - B depends on x */
static bool is_dep_lemma(type_context & ctx, expr const & e) {
    return
        is_pi(e) &&
        ctx.is_prop(e) &&
        ctx.is_prop(binding_domain(e)) &&
        !closed(binding_body(e));
}

static bool is_fact(type_context & ctx, expr const & e) {
    return ctx.is_prop(e) && !is_lemma(ctx, e) && !is_dep_lemma(ctx, e);
}

static expr flip(expr const & e) {
    expr not_e;
    if (is_not(e, not_e))
        return not_e;
    else
        return mk_not(e);
}

unit_propagation::unit_propagation(type_context & ctx, state & s, assignment & assignment):
    m_ctx(ctx), m_state(s), m_assignment(assignment) {}

void unit_propagation::internalize(expr const & /*e*/) {
    // TODO(Leo)
}

void unit_propagation::assignment_updated(expr const & /*e*/) {
    // TODO(Leo)
}
}

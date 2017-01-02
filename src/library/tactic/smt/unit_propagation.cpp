/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/util.h"
#include "library/trace.h"
#include "library/tactic/smt/unit_propagation.h"

namespace lean {
static bool is_lemma(type_context & ctx, expr e) {
    if (!ctx.is_prop(e)) return false;
    bool arrow = false;
    while (is_arrow(e) && !is_not(e)) {
        arrow = true;
        if (!ctx.is_prop(binding_domain(e))) return false;
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

unit_propagation::unit_propagation(type_context & ctx, state & s, assignment & assignment):
    m_ctx(ctx), m_state(s), m_assignment(assignment) {}

static expr get_var(expr const & e) {
    expr arg;
    if (is_not(e, arg))
        return arg;
    else
        return e;
}

void unit_propagation::visit_lemma(expr const & e) {
    lean_assert(is_lemma(ctx, e));
    expr it        = e;
    unsigned i     = 0;
    expr watches[2];

    /* Traverse A_i */
    while (is_arrow(it) && !is_not(it) && i < 2) {
        expr const & p = binding_domain(it);
        switch (get_value(p)) {
        case l_true:   break;
        case l_false: case l_undef:
            watches[i] = get_var(p);
            i++;
            break;
        }
        it = binding_body(it);
    }

    /* Traverse B_j */
    bool done = false;
    while (!done && i < 2) {
        expr p, next_it;
        if (is_or(it, p, next_it)) {
            it   = next_it;
        } else {
            p    = it;
            done = true;
        }
        switch (get_value(p)) {
        case l_false: break;
        case l_true: case l_undef:
            watches[i] = get_var(p);
            i++;
            break;
        }
    }

    if (i == 2) {
        m_state.m_facts_to_lemmas.insert(watches[0], e);
        m_state.m_facts_to_lemmas.insert(watches[1], e);
        return;
    }

    if (i == 0) return;

    /* TODO(Leo): */
}

void unit_propagation::visit_dep_lemma(expr const & /* e */) {
    /* TODO(Leo): */
}

void unit_propagation::propagate(expr const & e) {
    if (list<expr> const * lemmas = m_state.m_facts_to_lemmas.find(e)) {
        for (expr const & lemma : *lemmas)
            visit_lemma(lemma);
    }

    if (list<expr> const * lemmas = m_state.m_facts_to_dep_lemmas.find(e)) {
        for (expr const & lemma : *lemmas)
            visit_dep_lemma(lemma);
    }
}

void unit_propagation::assigned(expr const & e) {
    if (is_lemma(m_ctx, e) && m_assignment.get_value(e) == l_true) {
        visit_lemma(e);
    } else if (is_dep_lemma(m_ctx, e) && m_assignment.get_value(e) == l_true) {
        visit_dep_lemma(e);
    } else if (is_fact(m_ctx, e)) {
        propagate(e);
    }
}
}

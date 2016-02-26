/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/sstream.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/io_state_stream.h"
#include "library/tactic/proof_state.h"

#ifndef LEAN_PROOF_STATE_GOAL_NAMES
#define LEAN_PROOF_STATE_GOAL_NAMES false
#endif

#ifndef LEAN_PROOF_STATE_MINIMIZE_CONTEXTUAL
#define LEAN_PROOF_STATE_MINIMIZE_CONTEXTUAL true
#endif

namespace lean {
static name * g_proof_state_goal_names = nullptr;

bool get_proof_state_goal_names(options const & opts) {
    return opts.get_bool(*g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES);
}

proof_state::proof_state(goals const & gs, substitution const & s,
                         constraints const & postponed, bool report_failure):
    m_goals(gs), m_subst(s), m_postponed(postponed),
    m_report_failure(report_failure) {
    if (std::any_of(gs.begin(), gs.end(),
                    [&](goal const & g) { return s.is_assigned(g.get_mvar()); })) {
        m_goals = filter(gs, [&](goal const & g) { return !s.is_assigned(g.get_mvar()); });
    }
}

format proof_state::pp_core(std::function<formatter()> const & mk_fmt, options const & opts) const {
    bool show_goal_names = get_proof_state_goal_names(opts);
    unsigned indent      = get_pp_indent(opts);
    format r;
    bool first = true;

    for (auto const & g : get_goals()) {
        formatter fmt = mk_fmt();
        if (first) first = false; else r += line() + line();
        if (show_goal_names) {
            r += group(format(g.get_name()) + colon() + nest(indent, line() + g.pp(fmt, m_subst)));
        } else {
            r += g.pp(fmt, m_subst);
        }
    }
    if (first) r = format("no goals");
    return r;
}

format proof_state::pp(formatter const & fmt) const {
    return pp_core([&]() { return fmt; }, fmt.get_options());
}

goals map_goals(proof_state const & s, std::function<optional<goal>(goal const & g)> f) {
    return map_filter<goal>(s.get_goals(), [=](goal const & in, goal & out) -> bool {
            check_interrupted();
            optional<goal> new_goal = f(in);
            if (new_goal) {
                out = *new_goal;
                return true;
            } else {
                return false;
            }
        });
}

proof_state to_proof_state(expr const & meta, expr const & type, substitution const & subst) {
    return proof_state(goals(goal(meta, type)), subst, constraints());
}

proof_state to_proof_state(expr const & meta, expr const & type) {
    return to_proof_state(meta, type, substitution());
}

proof_state apply_substitution(proof_state const & s) {
    if (!s.get_goals())
        return s;
    substitution subst = s.get_subst();
    goal  g  = head(s.get_goals());
    goals gs = tail(s.get_goals());
    goal new_g(subst.instantiate_all(g.get_meta()), subst.instantiate_all(g.get_type()));
    return proof_state(s, goals(new_g, gs), subst);
}

void initialize_proof_state() {
    g_proof_state_goal_names = new name{"tactic", "goal_names"};
    register_bool_option(*g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES,
                         "(tactic) display goal names when pretty printing proof state");
}

void finalize_proof_state() {
    delete g_proof_state_goal_names;
}
}

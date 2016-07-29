/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sexpr/option_declarations.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/elaborator_context.h"
#include "frontends/lean/opt_cmd.h"

#ifndef LEAN_DEFAULT_ELABORATOR_FLYCHECK_GOALS
#define LEAN_DEFAULT_ELABORATOR_FLYCHECK_GOALS false
#endif

#ifndef LEAN_DEFAULT_ELABORATOR_LIFT_COERCIONS
#define LEAN_DEFAULT_ELABORATOR_LIFT_COERCIONS true
#endif

#ifndef LEAN_DEFAULT_ELABORATOR_COERCIONS
#define LEAN_DEFAULT_ELABORATOR_COERCIONS false
#endif


namespace lean {
// ==========================================
// elaborator configuration options
static name * g_elaborator_flycheck_goals     = nullptr;
static name * g_elaborator_lift_coercions     = nullptr;
static name * g_elaborator_coercions          = nullptr;

bool get_elaborator_flycheck_goals(options const & opts) {
    return opts.get_bool(*g_elaborator_flycheck_goals, LEAN_DEFAULT_ELABORATOR_FLYCHECK_GOALS);
}

bool get_elaborator_lift_coercions(options const & opts) {
    return opts.get_bool(*g_elaborator_lift_coercions, LEAN_DEFAULT_ELABORATOR_LIFT_COERCIONS);
}

bool get_elaborator_coercions(options const & opts) {
    return opts.get_bool(*g_elaborator_coercions, LEAN_DEFAULT_ELABORATOR_COERCIONS);
}

// ==========================================

elaborator_context::elaborator_context(environment const & env, options const & opts, local_level_decls const & lls,
                                       bool check_unassigned):
    m_env(env), m_lls(lls), m_check_unassigned(check_unassigned) {
    set_options(opts);
}

elaborator_context::elaborator_context(elaborator_context const & ctx, options const & o):
    m_env(ctx.m_env), m_lls(ctx.m_lls),
    m_check_unassigned(ctx.m_check_unassigned) {
    set_options(o);
}

void elaborator_context::set_options(options const & opts) {
    m_options             = opts;
    m_flycheck_goals      = get_elaborator_flycheck_goals(opts);
    m_lift_coercions      = get_elaborator_lift_coercions(opts);
    m_coercions           = get_elaborator_coercions(opts);

    if (has_show_goal(opts, m_show_goal_line, m_show_goal_col)) {
        m_show_goal_at = true;
    } else {
        m_show_goal_at = false;
    }

    if (has_show_hole(opts, m_show_hole_line, m_show_hole_col)) {
        m_show_hole_at = true;
    } else {
        m_show_hole_at = false;
    }
}

bool elaborator_context::has_show_goal_at(unsigned & line, unsigned & col) const {
    if (m_show_goal_at) {
        line = m_show_goal_line;
        col  = m_show_goal_col;
        return true;
    } else {
        return false;
    }
}

void elaborator_context::reset_show_goal_at() {
    m_show_goal_at = false;
}

bool elaborator_context::has_show_hole_at(unsigned & line, unsigned & col) const {
    if (m_show_hole_at) {
        line = m_show_hole_line;
        col  = m_show_hole_col;
        return true;
    } else {
        return false;
    }
}

void initialize_elaborator_context() {
    g_elaborator_flycheck_goals     = new name{"elaborator", "flycheck_goals"};
    g_elaborator_lift_coercions     = new name{"elaborator", "lift_coercions"};
    g_elaborator_coercions          = new name{"elaborator", "coercions"};
    register_bool_option(*g_elaborator_flycheck_goals, LEAN_DEFAULT_ELABORATOR_FLYCHECK_GOALS,
                         "(elaborator) if true, then elaborator display current goals for flycheck before each "
                         "tactic is executed in a `begin ... end` block");
    register_bool_option(*g_elaborator_lift_coercions, LEAN_DEFAULT_ELABORATOR_LIFT_COERCIONS,
                         "(elaborator) if true, the elaborator will automatically lift coercions from A to B "
                         "into coercions from (C -> A) to (C -> B)");
    register_bool_option(*g_elaborator_coercions, LEAN_DEFAULT_ELABORATOR_COERCIONS,
                         "(elaborator) if true, the elaborator will automatically introduce coercions");
}
void finalize_elaborator_context() {
    delete g_elaborator_flycheck_goals;
    delete g_elaborator_lift_coercions;
    delete g_elaborator_coercions;
}
}

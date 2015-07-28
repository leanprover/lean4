/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/info_manager.h"

namespace lean {
name const & get_elaborator_ignore_instances_name();
/** \brief Environment for elaboration, it contains all the information that is "scope-indenpendent" */
class elaborator_context {
    environment               m_env;
    io_state                  m_ios;
    local_decls<level>        m_lls; // local universe levels
    pos_info_provider const * m_pos_provider;
    info_manager *            m_info_manager;
    // configuration
    bool                      m_check_unassigned;
    bool                      m_use_local_instances;
    bool                      m_ignore_instances;
    bool                      m_flycheck_goals;
    bool                      m_fail_missing_field;
    bool                      m_lift_coercions;
    friend class elaborator;

    bool     m_show_goal_at;
    unsigned m_show_goal_line;
    unsigned m_show_goal_col;

    bool     m_show_hole_at;
    unsigned m_show_hole_line;
    unsigned m_show_hole_col;

    /** \brief Support for showing information using hot-keys */
    void init_options(options const & opts);
    bool has_show_goal_at(unsigned & line, unsigned & col) const;
    void reset_show_goal_at();

    bool has_show_hole_at(unsigned & line, unsigned & col) const;
    void reset_show_hole_at();
public:
    elaborator_context(environment const & env, io_state const & ios, local_decls<level> const & lls,
                       pos_info_provider const * pp = nullptr, info_manager * info = nullptr, bool check_unassigned = true);
};
void initialize_elaborator_context();
void finalize_elaborator_context();
}

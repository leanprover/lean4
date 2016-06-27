/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
#include "frontends/lean/local_level_decls.h"
#include "frontends/lean/info_manager.h"

namespace lean {
/** \brief Context for the elaborator.

    \remark It contains all the information that is "scope-indenpendent".
    So, it does not contain the local context because it is context dependent. */
class elaborator_context {
    friend class old_elaborator; // TODO(Leo): remove this line when done
    friend class elaborator;

    environment               m_env;
    local_level_decls         m_lls; // local universe levels
    pos_info_provider const * m_pos_provider;
    info_manager *            m_info_manager;
    // configuration
    options                   m_options;
    bool                      m_check_unassigned;
    bool                      m_flycheck_goals;
    bool                      m_lift_coercions;
    bool                      m_coercions;

    bool                      m_show_goal_at;
    unsigned                  m_show_goal_line;
    unsigned                  m_show_goal_col;

    bool                      m_show_hole_at;
    unsigned                  m_show_hole_line;
    unsigned                  m_show_hole_col;

    void set_options(options const & opts);

    /** \brief Support for showing information using hot-keys */
    bool has_show_goal_at(unsigned & line, unsigned & col) const;
    void reset_show_goal_at();

    bool has_show_hole_at(unsigned & line, unsigned & col) const;
public:
    elaborator_context(environment const & env, options const & opts, local_level_decls const & lls,
                       pos_info_provider const * pp = nullptr, info_manager * info = nullptr,
                       bool check_unassigned = true);
    elaborator_context(elaborator_context const & ctx, options const & o);
};
void initialize_elaborator_context();
void finalize_elaborator_context();
}

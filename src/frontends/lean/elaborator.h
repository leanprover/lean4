/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "util/list.h"
#include "kernel/environment.h"
#include "kernel/metavar.h"
#include "library/io_state.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/info_manager.h"

namespace lean {
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
    friend class elaborator;
public:
    elaborator_context(environment const & env, io_state const & ios, local_decls<level> const & lls,
                       pos_info_provider const * pp = nullptr, info_manager * info = nullptr, bool check_unassigned = true);
};

std::tuple<expr, level_param_names> elaborate(elaborator_context & env, list<expr> const & ctx, expr const & e,
                                              bool relax_main_opaque, bool ensure_type = false);

std::tuple<expr, expr, level_param_names> elaborate(elaborator_context & env, name const & n, expr const & t, expr const & v,
                                                    bool is_opaque);
void initialize_elaborator();
void finalize_elaborator();
}

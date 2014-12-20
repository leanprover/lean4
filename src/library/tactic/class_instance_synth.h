/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/io_state.h"
#include "library/unifier.h"

namespace lean {
class local_context;

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances.

    \param ctx Local context where placeholder is located
    \param prefix Prefix for metavariables that will be created by this procedure
    \param suffix If provided, then it is added to the main metavariable created by this procedure.
    \param relax True if opaque constants in the current module should be treated
                 as transparent
    \param use_local_instances If instances in the local context should be used
                               in the class-instance resolution
    \param is_strict True if constraint should fail if not solution is found,
                     False if empty solution should be returned if there is no solution
    \param type Expected type for the placeholder (if known)
    \param tag  To be associated with new metavariables and expressions (for error localization).
*/
pair<expr, constraint> mk_class_instance_elaborator(
    environment const & env, io_state const & ios, local_context const & ctx,
    name const & prefix, optional<name> const & suffix, bool relax_opaque, bool use_local_instances,
    bool is_strict, optional<expr> const & type, tag g, unifier_config const & cfg,
    pos_info_provider const * pip);

void initialize_class_instance_elaborator();
void finalize_class_instance_elaborator();
}

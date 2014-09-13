/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/unifier.h"

namespace lean {
/** \brief Create a metavariable m, and attach "choice" constraint that postpone the
    solving the constraints <tt>(cs union m =?= e)</tt>.
*/
pair<expr, constraint> mk_proof_qed_elaborator(environment const & env, local_context & ctx,
                                               expr const & e, optional<expr> const & type, constraint_seq const & cs,
                                               unifier_config const & cfg, bool relax);
}

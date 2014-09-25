/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/unifier.h"

namespace lean {
/** \brief Create a "choice" constraint that postpone the
    solving the constraints <tt>(cs union (m =?= e))</tt>.
*/
constraint mk_proof_qed_cnstr(environment const & env, expr const & m, expr const & e,
                              constraint_seq const & cs, unifier_config const & cfg, bool relax);
}

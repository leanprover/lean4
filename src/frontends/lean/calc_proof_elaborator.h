/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/unifier.h"
#include "frontends/lean/info_manager.h"

namespace lean {
/** \brief Create a "choice" constraint that postpones the resolution of a calc proof step.

    By delaying it, we can perform quick fixes such as:
      - adding symmetry
      - adding !
      - adding subst
*/
constraint mk_calc_proof_cnstr(environment const & env, local_context const & ctx,
                               expr const & m, expr const & e,
                               constraint_seq const & cs, unifier_config const & cfg,
                               info_manager * im, bool relax);
}

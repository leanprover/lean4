/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <functional>
#include "library/unifier.h"
#include "library/local_context.h"
#include "frontends/lean/info_manager.h"

namespace lean {
typedef std::function<void(expr const &)> update_type_info_fn;

/** \brief Create a "choice" constraint that postpones the resolution of a calc proof step.

    By delaying it, we can perform quick fixes such as:
      - adding symmetry
      - adding !
      - adding subst
*/
constraint mk_calc_proof_cnstr(environment const & env, options const & opts,
                               local_context const & ctx, expr const & m, expr const & e,
                               constraint_seq const & cs, unifier_config const & cfg,
                               info_manager * im, update_type_info_fn const & fn);

void initialize_calc_proof_elaborator();
void finalize_calc_proof_elaborator();
}

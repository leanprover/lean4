/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"

namespace lean {
expr const & get_exact_tac_fn();
expr const & get_sexact_tac_fn();
/** \brief Solve first goal iff it is definitionally equal to type of \c e */
void initialize_exact_tactic();
void finalize_exact_tactic();
}

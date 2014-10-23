/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/tactic/tactic.h"

namespace lean {
/** \brief Return a tactic that unfolds the definition named \c n. */
tactic unfold_tactic(name const & n);
/** \brief Return a tactic that unfolds all (non-opaque) definitions. */
tactic unfold_tactic();

void initialize_unfold_tactic();
void finalize_unfold_tactic();
}

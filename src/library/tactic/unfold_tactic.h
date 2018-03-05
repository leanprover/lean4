/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
/* Given (f ...), try to unfold it using (refl) equational lemmas for f. */
optional<expr> dunfold(type_context_old & ctx, expr const & e);
void initialize_unfold_tactic();
void finalize_unfold_tactic();
}

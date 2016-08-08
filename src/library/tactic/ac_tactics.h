/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"

namespace lean {
pair<expr, optional<expr>> flat_assoc(abstract_type_context & ctx, expr const & op, expr const & assoc, expr const & e);
/* Construct a proof that e1 = e2 modulo AC for the operator op. The proof uses the lemmas \c assoc and \c comm.
   It throws an exception if they are not equal modulo AC. */
expr perm_ac(abstract_type_context & ctx, expr const & op, expr const & assoc, expr const & comm, expr const & e1, expr const & e2);

void initialize_ac_tactics();
void finalize_ac_tactics();
}

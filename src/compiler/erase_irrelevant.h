/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Erase irrelevant terms (e.g., proofs, types, eq.rec, subtypes, etc).
    The parameters, motive and indices are also erased from cases_on applications.

    \remark The resultant term cannot be type checked. So, any preprocessing step
    that requires type inference cannot be applied after this transformation. */
expr erase_irrelevant(environment const & env, expr const & e);
/** \brief Neutral auxiliary term. */
bool is_neutral_term(expr const & e);

void initialize_erase_irrelevant();
void finalize_erase_irrelevant();
}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
/** \brief Return true if \c n is noncomputable */
bool is_noncomputable(environment const & env, name const & n);
/** \brief Mark \c n as noncomputable */
environment mark_noncomputable(environment const & env, name const & n);
/** \brief Throw an exception if \c n depends on a noncomputable definition */
void validate_computable_definition(environment const & env, name const & n);
void initialize_noncomputable();
void finalize_noncomputable();
}

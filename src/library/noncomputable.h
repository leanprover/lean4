/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
bool is_marked_noncomputable(environment const & env, name const & n);
/** \brief Return true if \c n is noncomputable */
bool is_noncomputable(environment const & env, name const & n);
/** \brief Mark \c n as noncomputable */
environment mark_noncomputable(environment const & env, name const & n);
/** \brief In standard mode, check if definitions that are not propositions can compute */
bool check_computable(environment const & env, name const & n);
optional<name> get_noncomputable_reason(environment const & env, name const & n);
void initialize_noncomputable();
void finalize_noncomputable();
}

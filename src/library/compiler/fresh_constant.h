/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

namespace lean {
/** \brief Create a new constant name that is not used by \c env.
    A new environment is returned. The new environment is semantically identical to \c env, but
    internal counters are updated to make sure the fresh constant can be efficiently generated. */
pair<environment, name> mk_fresh_constant(environment const & env);

/** \brief Similar to the previous method, but the new constant uses the given prefix.
    \pre \c prefix must start with '_'. */
pair<environment, name> mk_fresh_constant(environment const & env, char const * prefix);

void initialize_fresh_constant();
void finalize_fresh_constant();
}

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
/* Common subexpression elimination */
expr cse_core(elab_environment const & env, expr const & e, bool before_erasure);
inline expr cse(elab_environment const & env, expr const & e) { return cse_core(env, e, true); }
inline expr ecse(elab_environment const & env, expr const & e) { return cse_core(env, e, false); }
/* Common case elimination */
expr cce_core(elab_environment const & env, local_ctx const & lctx, expr const & e);
inline expr cce(elab_environment const & env, expr const & e) { return cce_core(env, local_ctx(), e); }
void initialize_cse();
void finalize_cse();
}

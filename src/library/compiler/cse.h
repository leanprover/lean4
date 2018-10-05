/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
/* Common subexpression elimination */
expr cse(environment const & env, expr const & e);
/* Common case elimination */
expr cce_core(environment const & env, local_ctx const & lctx, expr const & e);
inline expr cce(environment const & env, expr const & e) { return cce_core(env, local_ctx(), e); }
void initialize_cse();
void finalize_cse();
}

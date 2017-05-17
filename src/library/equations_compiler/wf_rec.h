/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
expr wf_rec(environment & env, options const & opts,
            metavar_context & mctx, local_context const & lctx,
            expr const & eqns);
void initialize_wf_rec();
void finalize_wf_rec();
}

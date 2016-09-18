/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
namespace lean {
/** \brief Eliminate "recursive calls" using rec_fn_macro.

    This compilation step can only be used to compile meta definitions.
    If we use it on regular definitions, the kernel will reject it. */
expr unbounded_rec(environment & env, options const & opts,
                   metavar_context & mctx, local_context const & lctx,
                   expr const & eqns);
}

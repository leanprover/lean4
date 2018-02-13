/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/equations_compiler/util.h"
namespace lean {
class elaborator;
/** \brief Eliminate "recursive calls" using rec_fn_macro.

    This compilation step can only be used to compile meta definitions.
    If we use it on regular definitions, the kernel will reject it. */
eqn_compiler_result unbounded_rec(environment & env, elaborator & elab,
                                  metavar_context & mctx, local_context const & lctx,
                                  expr const & eqns);
}

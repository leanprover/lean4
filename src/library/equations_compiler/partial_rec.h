/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/equations_compiler/util.h"
namespace lean {
class elaborator;
/** \brief Eliminate "recursive calls" using "fuel". */
eqn_compiler_result partial_rec(environment & env, elaborator & elab,
                                metavar_context & mctx, local_context const & lctx,
                                expr const & eqns);
}

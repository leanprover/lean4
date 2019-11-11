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
/** \brief Eliminate "recursive calls" using unbounded recursion.

    This compilation step can only be used to compile unsafe definitions.
    If we use it on regular definitions, the kernel will reject it.

    Remark: If `eqns` has already been compiled in safe mode,
    then `safe_result` contains the result of the compilation.
    We need this information to make sure the type of the auxiliary `_unsafe_rec` definitions
    match the type of the regular ones.
*/
eqn_compiler_result unbounded_rec(environment & env, elaborator & elab,
                                  metavar_context & mctx, local_context const & lctx,
                                  expr const & eqns, optional<expr> const & safe_result = optional<expr>());
}

/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/type_context.h"
#include "library/equations_compiler/util.h"
namespace lean {
class elaborator;
eqn_compiler_result wf_rec(environment & env, elaborator & elab,
                           metavar_context & mctx, local_context const & lctx,
                           expr const & eqns);

/* Return true if definition `n` was compiled by equation compiler using
   well_founded recursion. */
bool uses_well_founded_recursion(environment const & env, name const & n);

void initialize_wf_rec();
void finalize_wf_rec();
}

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
*/
#pragma once
#include "library/compiler/util.h"
namespace lean {
comp_decls reduce_arity(elab_environment const & env, comp_decls const & cdecls);
/* Return true if the `cdecl` is of the form `f := fun xs, f._rarg ...`.
   That is, `f`s arity "was reduced" and an auxiliary declaration `f._rarg` was created to replace it. */
bool arity_was_reduced(comp_decl const & cdecl);
}

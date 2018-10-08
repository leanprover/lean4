/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/util.h"
namespace lean {
/** \brief Lift lambda expressions in `cdecl`. The result contains `cdecl` after lambda lifting and the new auxiliary declarations that have been generated. */
comp_decls lambda_lifting(environment const & env, comp_decl const & cdecl);
};

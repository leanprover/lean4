/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/compiler/util.h"
#include "library/compiler/csimp.h"
namespace lean {
pair<environment, comp_decls> specialize(environment env, comp_decls const & ds, csimp_cfg const & cfg);
void initialize_specialize();
void finalize_specialize();
}

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
namespace lean {
expr erase_irrelevant_core(elab_environment const & env, local_ctx const & lctx, expr const & e);
inline expr erase_irrelevant(elab_environment const & env, expr const & e) { return erase_irrelevant_core(env, local_ctx(), e); }
}

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
expr to_lcnf(environment const & env, local_ctx const & lctx, expr const & e);
void initialize_lcnf();
void finalize_lcnf();
}

/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
namespace lean {
expr ll_infer_type(environment const & env, local_ctx const & lctx, expr const & e);
inline expr ll_infer_type(environment const & env, expr const & e) { return ll_infer_type(env, local_ctx(), e); }
}

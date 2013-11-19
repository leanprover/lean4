/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/**
   \brief Return true iff \c e contains a constant with a cached type.

   The kernel should *not* accept expressions containing cached types.
   Reason: Cached types may introduce unsoundness.
   For example, in the environment env, the constant x may have type T.
   Now suppose we are trying to add a new definition D that contains x,
   and x is associated with a cached type T'. The cached type may allow
   us to accept a definition that is type incorrect with respect to env.
*/
bool has_cached_type(expr const & e);
}

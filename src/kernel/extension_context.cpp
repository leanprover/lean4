/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/extension_context.h"
#include "kernel/expr.h"

namespace lean {
expr extension_context::whnf(expr const & e, constraint_seq & cs) {
    auto p = whnf(e); cs += p.second; return p.first;
}
expr extension_context::infer_type(expr const & e, constraint_seq & cs) {
    auto p = infer_type(e); cs += p.second; return p.first;
}
}

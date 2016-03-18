/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/extension_context.h"
#include "kernel/expr.h"

namespace lean {
expr extension_context::infer_type(expr const & e) {
    bool infer_only = true;
    return check_type(e, infer_only);
}
}

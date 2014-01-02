/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/expr_pair.h"
#include "kernel/builtin.h"

namespace lean {
bool is_eq_heq(expr const & e) {
    return is_eq(e) || is_homo_eq(e);
}

expr_pair eq_heq_args(expr const & e) {
    lean_assert(is_eq(e) || is_homo_eq(e));
    if (is_eq(e))
        return expr_pair(eq_lhs(e), eq_rhs(e));
    else
        return expr_pair(arg(e, 2), arg(e, 3));
}
}

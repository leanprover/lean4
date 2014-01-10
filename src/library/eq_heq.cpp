/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/expr_pair.h"
#include "kernel/builtin.h"

namespace lean {
bool is_eq_heq(expr const & e) {
    return is_heq(e) || is_eq(e);
}

expr_pair eq_heq_args(expr const & e) {
    lean_assert(is_heq(e) || is_eq(e));
    if (is_heq(e))
        return expr_pair(heq_lhs(e), heq_rhs(e));
    else
        return expr_pair(arg(e, 2), arg(e, 3));
}
}

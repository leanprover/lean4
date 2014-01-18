/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/kernel.h"
#include "library/expr_pair.h"

namespace lean {
bool is_equality(expr const & e) {
    return is_eq(e) || is_iff(e);
}

bool is_equality(expr const & e, expr & lhs, expr & rhs) {
    if (is_eq(e) || is_iff(e)) {
        unsigned num = num_args(e);
        lhs = arg(e, num - 2);
        rhs = arg(e, num - 1);
        return true;
    } else {
        return false;
    }
}

expr_pair get_equality_args(expr const & e) {
    unsigned num = num_args(e);
    return mk_pair(arg(e, num - 2), arg(e, num - 1));
}
}

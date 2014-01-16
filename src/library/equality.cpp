/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/expr_pair.h"
#include "kernel/kernel.h"

namespace lean {
bool is_equality(expr const & e) {
    return is_eq(e) || is_iff(e) || is_heq(e);
}

bool is_equality(expr const & e, expr & lhs, expr & rhs) {
    if (is_eq(e)) {
        lhs = arg(e, 2);
        rhs = arg(e, 3);
        return true;
    } else if (is_iff(e)) {
        lhs = arg(e, 1);
        rhs = arg(e, 2);
        return true;
    } else if (is_heq(e)) {
        lhs = heq_lhs(e);
        rhs = heq_rhs(e);
        return true;
    } else {
        return false;
    }
}

expr_pair get_equality_args(expr const & e) {
    if (is_eq(e)) {
        return mk_pair(arg(e, 2), arg(e, 3));
    } else if (is_iff(e)) {
        return mk_pair(arg(e, 1), arg(e, 2));
    } else if (is_heq(e)) {
        return mk_pair(heq_lhs(e), heq_rhs(e));
    } else {
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}
}

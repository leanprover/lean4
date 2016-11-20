/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief If 'a' and 'b' are two distinct natural number values, then return a proof
    they are disequal. Otherwise return none.

    \remark This function assumes 'a' and 'b' have type nat.

    \remark A natural number value is any expression built using
    bit0, bit1, zero, one, nat.succ and nat.zero */
optional<expr> mk_nat_val_ne_proof(expr const & a, expr const & b);
}

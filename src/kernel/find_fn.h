/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/for_each_fn.h"
#include "kernel/expr.h"

namespace lean {
/** \brief Return a subexpression of \c e that satisfies the predicate \c p. */
template<typename P> optional<expr> find(expr const & e, P p) {
    optional<expr> result;
    for_each(e, [&](expr const & e, unsigned offset) {
            if (result)  {
                return false;
            } else if (p(e, offset)) {
                result = e;
                return false;
            } else {
                return true;
            }
        });
    return result;
}
}

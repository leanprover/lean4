/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/expr.h"
#include "kernel/for_each_fn.h"

namespace lean {
bool has_cached_type(expr const & e) {
    bool result = false;
    auto f = [&](expr const & e, unsigned) {
        if (result) {
            return false; // do not continue the search
        } else if (is_constant(e) && const_type(e)) {
            result = true;
            return false;
        } else {
            return true;
        }
    };
    for_each_fn<decltype(f)> proc(f);
    proc(e);
    return result;
}
}

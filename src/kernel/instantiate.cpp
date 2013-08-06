/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "free_vars.h"
#include "replace.h"

namespace lean {
expr instantiate_with_closed(expr const & e, unsigned n, expr const * s) {
    lean_assert(std::all_of(s, s+n, closed));

    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx >= offset) {
                if (vidx < offset + n)
                    return s[n - (vidx - offset) - 1];
                else
                    return mk_var(vidx - n);
            }
        }
        return e;
    };
    return replace_fn<decltype(f)>(f)(e);
}
expr instantiate(expr const & e, unsigned n, expr const * s) {
    auto f = [=](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx >= offset) {
                if (vidx < offset + n)
                    return lift_free_vars(s[n - (vidx - offset) - 1], offset);
                else
                    return mk_var(vidx - n);
            }
        }
        return e;
    };
    return replace_fn<decltype(f)>(f)(e);
}
}

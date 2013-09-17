/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/free_vars.h"
#include "kernel/replace.h"
#include "kernel/metavar.h"

namespace lean {
expr instantiate_with_closed(expr const & a, unsigned n, expr const * s) {
    lean_assert(std::all_of(s, s+n, closed));

    auto f = [=](expr const & m, unsigned offset) -> expr {
        if (is_var(m)) {
            unsigned vidx = var_idx(m);
            if (vidx >= offset) {
                if (vidx < offset + n)
                    return s[n - (vidx - offset) - 1];
                else
                    return mk_var(vidx - n);
            } else {
                return m;
            }
        } else if (is_metavar(m)) {
            expr r = m;
            for (unsigned i = 0; i < n; i++)
                r = add_inst(r, offset + n - i - 1, s[i]);
            return r;
        } else {
            return m;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}
expr instantiate(expr const & a, unsigned s, unsigned n, expr const * subst) {
    auto f = [=](expr const & m, unsigned offset) -> expr {
        if (is_var(m)) {
            unsigned vidx = var_idx(m);
            if (vidx >= offset + s) {
                if (vidx < offset + s + n)
                    return lift_free_vars(subst[n - (vidx - s - offset) - 1], offset);
                else
                    return mk_var(vidx - n);
            } else {
                return m;
            }
        } else if (is_metavar(m)) {
            expr r = m;
            for (unsigned i = 0; i < n; i++)
                r = add_inst(r, offset + s + n - i - 1, lift_free_vars(subst[i], offset + n - i - 1));
            return r;
        } else {
            return m;
        }
    };
    return replace_fn<decltype(f)>(f)(a);
}
expr instantiate(expr const & e, unsigned n, expr const * s) {
    return instantiate(e, 0, n, s);
}
expr instantiate(expr const & e, unsigned i, expr const & s) {
    return instantiate(e, i, 1, &s);
}
}

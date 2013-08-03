/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "free_vars.h"
#include "replace.h"

namespace lean {
expr abstract(expr const & e, unsigned n, expr const * s) {
    lean_assert(std::all_of(s, s+n, closed));

    auto f = [=](expr const & e, unsigned offset) -> expr {
        unsigned i = n;
        while (i > 0) {
            --i;
            if (s[i] == e)
                return var(offset + n - i - 1);
        }
        return e;
    };

    return replace_fn<decltype(f)>(f)(e);
}
expr abstract_p(expr const & e, unsigned n, expr const * s) {
    lean_assert(std::all_of(s, s+n, closed));

    auto f = [=](expr const & e, unsigned offset) -> expr {
        unsigned i = n;
        while (i > 0) {
            --i;
            if (eqp(s[i], e))
                return var(offset + n - i - 1);
        }
        return e;
    };

    return replace_fn<decltype(f)>(f)(e);
}
}

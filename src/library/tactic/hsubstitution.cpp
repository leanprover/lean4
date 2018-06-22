/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace_fn.h"
#include "library/tactic/hsubstitution.h"

namespace lean {
expr apply(expr const & e, hsubstitution const & s) {
    if (s.empty()) return e;
    if (!has_local(e)) return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_local(e)) return some_expr(e);
            if (is_local(e)) {
                if (auto r = s.find(local_name(e)))
                    return some_expr(*r);
            }
            return none_expr();
        });
}

list<expr> apply(list<expr> const & es, hsubstitution const & s) {
    if (s.empty()) return es;
    return map(es, [&](expr const & e) { return apply(e, s); });
}

hsubstitution apply(hsubstitution const & s1, hsubstitution const & s2) {
    if (s2.empty()) return s1;
    hsubstitution R;
    s1.for_each([&](name const & x, expr const & e) {
            R.insert(x, apply(e, s2));
        });
    return R;
}

hsubstitution merge(hsubstitution const & s1, hsubstitution const & s2) {
    if (s1.empty()) return s2;
    if (s2.empty()) return s1;
    hsubstitution R = s1;
    s2.for_each([&](name const & x, expr const & e) {
            R.insert(x, e);
        });
    return R;
}
}

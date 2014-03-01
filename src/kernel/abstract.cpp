/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "kernel/replace_fn.h"

namespace lean {
expr abstract(expr const & e, unsigned n, expr const * s) {
    lean_assert(std::all_of(s, s+n, closed));
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned i = n;
            while (i > 0) {
                --i;
                if (s[i] == e)
                    return some_expr(mk_var(offset + n - i - 1));
            }
            return none_expr();
        });
}
expr abstract_p(expr const & e, unsigned n, expr const * s) {
    lean_assert(std::all_of(s, s+n, closed));
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            unsigned i = n;
            while (i > 0) {
                --i;
                if (is_eqp(s[i], e))
                    return some_expr(mk_var(offset + n - i - 1));
            }
            return none_expr();
        });
}
#define MkBinder(FName)                                                 \
expr FName(std::initializer_list<std::pair<expr const &, expr const &>> const & l, expr const & b) { \
    expr r = b;                                                         \
    auto it = l.end();                                                  \
    while (it != l.begin()) {                                           \
        --it;                                                           \
        auto const & p = *it;                                           \
        r = FName(p.first, p.second, r);                                \
    }                                                                   \
    return r;                                                           \
}

MkBinder(Fun);
MkBinder(Pi);
}

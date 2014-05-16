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
expr abstract(expr const & e, unsigned s, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, closed));
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            if (closed(e)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (subst[i] == e)
                        return some_expr(mk_var(offset + s + n - i - 1));
                }
            }
            return none_expr();
        });
}
expr abstract(expr const & e, unsigned n, expr const * subst) { return abstract(e, 0, n, subst); }

telescope abstract(telescope const & t, expr const & s, unsigned i) {
    if (is_nil(t)) {
        return t;
    } else {
        binder const & b = head(t);
        return telescope(b.update_type(abstract(b.get_type(), i, 1, &s)),
                         abstract(head(t), s, i+1));
    }
}

telescope abstract(telescope const & t, expr const & s) { return abstract(t, s, 0); }


expr abstract_p(expr const & e, unsigned n, expr const * s) {
    lean_assert(std::all_of(s, s+n, closed));
    return replace(e, [=](expr const & e, unsigned offset) -> optional<expr> {
            if (closed) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (is_eqp(s[i], e))
                        return some_expr(mk_var(offset + n - i - 1));
                }
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

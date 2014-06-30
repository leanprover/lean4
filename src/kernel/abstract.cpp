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
                        return some_expr(copy_tag(e, mk_var(offset + s + n - i - 1)));
                }
            }
            return none_expr();
        });
}
expr abstract(expr const & e, unsigned n, expr const * subst) { return abstract(e, 0, n, subst); }
expr abstract(expr const & e, expr const & s, unsigned i) { return abstract(e, i, 1, &s); }

expr abstract_locals(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return closed(e) && is_local(e); }));
    if (!has_local(e))
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
            if (!has_local(m))
                return some_expr(m); // expression m does not contain local constants
            if (is_local(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (mlocal_name(subst[i]) == mlocal_name(m))
                        return some_expr(copy_tag(m, mk_var(offset + n - i - 1)));
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

#define MkBinder2(FName, Mk)                                            \
expr FName(unsigned num, expr const * locals, expr const & b) {         \
    expr r = b;                                                         \
    unsigned i = num;                                                   \
    while (i > 0) {                                                     \
        --i;                                                            \
        r = Mk(local_pp_name(locals[i]), mlocal_type(locals[i]), abstract(r, locals[i])); \
    }                                                                   \
    return r;                                                           \
}

MkBinder2(Fun, mk_lambda);
MkBinder2(Pi, mk_pi);
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <utility>
#include <vector>
#include "kernel/abstract.h"
#include "kernel/free_vars.h"
#include "kernel/replace_fn.h"

namespace lean {
expr abstract(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return closed(e) && is_local(e); }));
#ifndef LEAN_NO_HAS_LOCAL_OPT
    if (!has_local(e))
        return e;
#endif
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
#ifndef LEAN_NO_HAS_LOCAL_OPT
            if (!has_local(m))
                return some_expr(m); // expression m does not contain local constants
#endif
            if (is_local(m)) {
                unsigned i = n;
                while (i > 0) {
                    --i;
                    if (mlocal_name(subst[i]) == mlocal_name(m))
                        return some_expr(mk_var(offset + n - i - 1, m.get_tag()));
                }
                return none_expr();
            }
            return none_expr();
        });
}

expr abstract(expr const & e, name const & l) {
    expr dummy = mk_Prop();
    expr local = mk_local(l, dummy);
    return abstract(e, 1, &local);
}

template<bool is_lambda>
expr mk_binding(unsigned num, expr const * locals, expr const & b) {
    expr r     = abstract(b, num, locals);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = abstract(mlocal_type(l), i, locals);
        if (is_lambda)
            r = mk_lambda(mlocal_pp_name(l), t, r, local_info(l));
        else
            r = mk_pi(mlocal_pp_name(l), t, r, local_info(l));
    }
    return r;
}

expr Pi(unsigned num, expr const * locals, expr const & b) { return mk_binding<false>(num, locals, b); }
expr Fun(unsigned num, expr const * locals, expr const & b) { return mk_binding<true>(num, locals, b); }
}

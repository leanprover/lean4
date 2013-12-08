/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/context_to_lambda.h"

namespace lean {
static expr g_fake = Const(name::mk_internal_unique_name());
expr context_to_lambda(context::iterator it, context::iterator const & end, expr const & e) {
    if (it == end) {
        return e;
    } else {
        context_entry const & entry = *it;
        optional<expr> t;
        optional<expr> const & d = entry.get_domain();
        optional<expr> const & b = entry.get_body();
        lean_assert(b || d);
        if (b && d)
            t = mk_app(g_fake, *d, *b);
        else if (d)
            t = mk_app(g_fake, *d, g_fake);
        else
            t = mk_app(g_fake, g_fake, *b);
        lean_assert(t);
        return context_to_lambda(++it, end, mk_lambda(entry.get_name(), *t, e));
    }
}
expr context_to_lambda(context const & c, expr const & e) {
    return context_to_lambda(c.begin(), c.end(), e);
}
bool is_fake_context(expr const & e) {
    return is_lambda(e) && is_app(abst_domain(e)) && arg(abst_domain(e), 0) == g_fake;
}
name const & fake_context_name(expr const & e) {
    lean_assert(is_fake_context(e));
    return abst_name(e);
}
optional<expr> fake_context_domain(expr const & e) {
    lean_assert(is_fake_context(e));
    expr r = arg(abst_domain(e), 1);
    if (!is_eqp(r, g_fake))
        return optional<expr>(r);
    else
        return optional<expr>();
}
optional<expr> fake_context_value(expr const & e) {
    lean_assert(is_fake_context(e));
    expr r = arg(abst_domain(e), 2);
    if (!is_eqp(r, g_fake))
        return optional<expr>(r);
    else
        return optional<expr>();
}
expr const & fake_context_rest(expr const & e) {
    return abst_body(e);
}
}

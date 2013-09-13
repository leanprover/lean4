/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/context_to_lambda.h"

namespace lean {
static expr g_fake = Const(name(name(0u), "context_to_lambda"));
expr context_to_lambda(context::iterator it, context::iterator const & end, expr const & e) {
    if (it == end) {
        return e;
    } else {
        context_entry const & entry = *it;
        expr t;
        if (entry.get_body())
            t = mk_app(g_fake, entry.get_domain(), entry.get_body());
        else
            t = mk_app(g_fake, entry.get_domain());
        return context_to_lambda(++it, end, mk_lambda(entry.get_name(), t, e));
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
expr const & fake_context_domain(expr const & e) {
    lean_assert(is_fake_context(e));
    return arg(abst_domain(e), 1);
}
expr const & fake_context_value(expr const & e) {
    lean_assert(is_fake_context(e));
    if (num_args(abst_domain(e)) > 2)
        return arg(abst_domain(e), 2);
    else
        return expr::null();
}
expr const & fake_context_rest(expr const & e) {
    return abst_body(e);
}
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/occurs.h"
#include "kernel/metavar.h"
#include "kernel/expr_maps.h"
#include "library/replace_using_ctx.h"
#include "library/placeholder.h"

namespace lean {
static name g_placeholder_name("_");
expr mk_placholder() {
    return mk_constant(g_placeholder_name);
}

bool is_placeholder(expr const & e) {
    return is_constant(e) && const_name(e) == g_placeholder_name;
}

bool has_placeholder(expr const & e) {
    return occurs(mk_placholder(), e);
}

expr replace_placeholders_with_metavars(expr const & e, metavar_env & menv, expr_map<expr> * new2old) {
    auto f = [&](expr const & e, context const & c, unsigned) -> expr {
        if (is_placeholder(e)) {
            return menv.mk_metavar(c);
        } else {
            return e;
        }
    };
    auto p = [&](expr const & s, expr const & t) {
        if (new2old)
            (*new2old)[t] = s;
    };
    return replace_using_ctx_fn<decltype(f), decltype(p)>(f, p)(e);
}
}

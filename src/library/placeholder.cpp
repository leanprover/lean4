/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/occurs.h"
#include "kernel/metavar.h"
#include "kernel/expr_maps.h"
#include "kernel/replace.h"
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

expr replace_placeholders_with_metavars(expr const & e, metavar_generator & mgen, expr_map<expr> * trace) {
    auto f = [&](expr const & e, unsigned) -> expr {
        if (is_placeholder(e)) {
            return mgen.mk();
        } else {
            return e;
        }
    };
    auto p = [&](expr const & s, expr const & t) {
        if (trace)
            (*trace)[t] = s;
    };
    return replace_fn<decltype(f), decltype(p)>(f, p)(e);
}
}

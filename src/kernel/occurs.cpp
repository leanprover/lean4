/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/occurs.h"
#include "kernel/find_fn.h"

namespace lean {
bool occurs(name const & n, context const * c, unsigned sz, expr const * es) {
    return find(c, sz, es, [&](expr const & e) { return is_constant(e) && const_name(e) == n; });
}

bool occurs(expr const & n, context const * c, unsigned sz, expr const * es) {
    return find(c, sz, es, [&](expr const & e) { return e == n; });
}
bool occurs(expr const & n, expr const & m) { return occurs(n, nullptr, 1, &m); }
bool occurs(name const & n, expr const & m) { return occurs(n, nullptr, 1, &m); }
bool occurs(expr const & n, context const & c) { return occurs(n, &c, 0, nullptr); }
bool occurs(name const & n, context const & c) { return occurs(n, &c, 0, nullptr); }
bool occurs(expr const & n, context const & c, unsigned sz, expr const * es) { return occurs(n, &c, sz, es); }
bool occurs(name const & n, context const & c, unsigned sz, expr const * es) { return occurs(n, &c, sz, es); }
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/occurs.h"
#include "kernel/for_each.h"

namespace lean {
template<typename F>
void for_each(F & f, context const * c, unsigned sz, expr const * es) {
    for_each_fn<F> visitor(f);
    if (c) {
        for (auto const & e : *c) {
            visitor(e.get_domain());
            if (e.get_body())
                visitor(e.get_body());
        }
    }
    for (unsigned i = 0; i < sz; i++)
        visitor(es[i]);
}

namespace occurs_ns {
/** \brief Auxiliary struct used to sign (as an exception) that an occurrence was found. */
struct found {};
}
bool occurs(name const & n, context const * c, unsigned sz, expr const * es) {
    auto visitor = [&](expr const & e, unsigned) -> void {
        if (is_constant(e)) {
            if (const_name(e) == n)
                throw occurs_ns::found();
        }
    };
    try {
        for_each(visitor, c, sz, es);
        return false;
    } catch (occurs_ns::found) {
        return true;
    }
}

bool occurs(expr const & n, context const * c, unsigned sz, expr const * es) {
    auto visitor = [&](expr const & e, unsigned) -> void {
        if (e == n)
            throw occurs_ns::found();
    };
    try {
        for_each(visitor, c, sz, es);
        return false;
    } catch (occurs_ns::found) {
        return true;
    }
}

bool occurs(expr const & n, expr const & m) { return occurs(n, nullptr, 1, &m); }
bool occurs(name const & n, expr const & m) { return occurs(n, nullptr, 1, &m); }
bool occurs(expr const & n, context const & c) { return occurs(n, &c, 0, nullptr); }
bool occurs(name const & n, context const & c) { return occurs(n, &c, 0, nullptr); }
bool occurs(expr const & n, context const & c, unsigned sz, expr const * es) { return occurs(n, &c, sz, es); }
bool occurs(name const & n, context const & c, unsigned sz, expr const * es) { return occurs(n, &c, sz, es); }
}

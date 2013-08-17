/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "context.h"
#include "occurs.h"
#include "exception.h"

namespace lean {
context sanitize_names_core(context const & c, context const & r, unsigned sz, expr const * es) {
    if (is_nil(c)) {
        return c;
    } else {
        // Remark: if this code is a bottleneck, then we can collect
        // all used names in r and es[sz] once and avoid the multiple
        // calls to occurs.
        context new_tail = sanitize_names_core(tail(c), r, sz, es);
        context_entry const & e = head(c);
        name const & n = e.get_name();
        name n1    = n;
        unsigned i = 1;
        while (occurs(n1, r, sz, es) ||
               std::any_of(new_tail.begin(), new_tail.end(), [&](context_entry const & e2) { return n1 == e2.get_name(); })) {
            n1 = name(n, i);
            i++;
        }
        return extend(new_tail, n1, e.get_domain(), e.get_body());
    }
}

context sanitize_names(context const & c, unsigned sz, expr const * es) {
    return sanitize_names_core(c, c, sz, es);
}

std::pair<context_entry const &, context const &> lookup_ext(context const & c, unsigned i) {
    context const * it1 = &c;
    while (*it1) {
        if (i == 0)
            return std::pair<context_entry const &, context const &>(head(*it1), tail(*it1));
        --i;
        it1 = &tail(*it1);
    }
    throw exception("unknown free variable");
}

context_entry const & lookup(context const & c, unsigned i) {
    context const * it1 = &c;
    while (*it1) {
        if (i == 0)
            return head(*it1);
        --i;
        it1 = &tail(*it1);
    }
    throw exception("unknown free variable");
}
}

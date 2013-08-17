/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "context.h"
#include "exception.h"

namespace lean {
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

/**
    \brief Return a new context where the names used in the context
    entries of \c c do not shadow constants occurring in \c c and \c es[sz].

    Recall that the names in context entries are just "suggestions".
    These names are used to name free variables in \c es[sz] (and
    dependent entries in \c c).
*/
context sanitize_names(context const & c, unsigned sz, expr const * es);
inline context sanitize_names(context const & c, expr const & e) { return sanitize_names(c, 1, &e); }
inline context sanitize_names(context const & c, std::initializer_list<expr> const & l) { return sanitize_names(c, l.size(), l.begin()); }

}

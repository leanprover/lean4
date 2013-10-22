/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/exception.h"
#include "kernel/context.h"

namespace lean {
std::pair<context_entry const &, context> context::lookup_ext(unsigned i) const {
    list<context_entry> const * it1 = &m_list;
    while (*it1) {
        if (i == 0)
            return std::pair<context_entry const &, context>(head(*it1), context(tail(*it1)));
        --i;
        it1 = &tail(*it1);
    }
    throw exception("unknown free variable");
}

context_entry const & context::lookup(unsigned i) const {
    list<context_entry> const * it1 = &m_list;
    while (*it1) {
        if (i == 0)
            return head(*it1);
        --i;
        it1 = &tail(*it1);
    }
    throw exception("unknown free variable");
}

static list<context_entry> remove_core(list<context_entry> const & l, unsigned s, unsigned n) {
    if (s == 0) {
        if (n > 0) {
            return remove_core(tail(l), 0, n-1);
        } else {
            return l;
        }
    } else {
        return cons(head(l), remove_core(tail(l), s-1, n));
    }
}

context context::remove(unsigned s, unsigned n) const {
    return context(remove_core(m_list, s, n));
}
}

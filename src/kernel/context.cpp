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

optional<context_entry> context::find(unsigned i) const {
    list<context_entry> const * it1 = &m_list;
    while (*it1) {
        if (i == 0)
            return some(head(*it1));
        --i;
        it1 = &tail(*it1);
    }
    return optional<context_entry>();
}

static list<context_entry> remove_core(list<context_entry> const & l, unsigned s, unsigned n) {
    if (l) {
        if (s == 0) {
            if (n > 0) {
                return remove_core(tail(l), 0, n-1);
            } else {
                return l;
            }
        } else {
            return cons(head(l), remove_core(tail(l), s-1, n));
        }
    } else {
        return l;
    }
}

context context::remove(unsigned s, unsigned n) const {
    return context(remove_core(m_list, s, n));
}

static list<context_entry> insert_at_core(list<context_entry> const & l, unsigned i, name const & n, expr const & d) {
    if (i == 0) {
        return cons(context_entry(n, d), l);
    } else {
        lean_assert(l);
        return cons(head(l), insert_at_core(tail(l), i - 1, n, d));
    }
}

context context::insert_at(unsigned i, name const & n, expr const & d) const {
    return context(insert_at_core(m_list, i, n, d));
}
}

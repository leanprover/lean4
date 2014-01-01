/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/exception.h"
#include "kernel/context.h"
#include "kernel/metavar.h"
#include "kernel/free_vars.h"

namespace lean {
context::context(std::initializer_list<std::pair<char const *, expr const &>> const & l) {
    for (auto const & p : l)
        m_list = cons(context_entry(name(p.first), p.second), m_list);
}

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

list<context_entry> truncate_core(list<context_entry> const & l, unsigned s) {
    if (s == 0) {
        return list<context_entry>();
    } else {
        return cons(head(l), truncate_core(tail(l), s-1));
    }
}

context context::truncate(unsigned s) const {
    return context(truncate_core(m_list, s));
}

struct remove_no_applicable {};
static list<context_entry> remove_core(list<context_entry> const & l, unsigned s, unsigned n, metavar_env const & menv) {
    if (l) {
        if (s == 0) {
            if (n > 0) {
                return remove_core(tail(l), 0, n-1, menv);
            } else {
                return l;
            }
        } else {
            if (has_free_var(head(l), s-1, s+n-1, menv))
                throw remove_no_applicable();
            return cons(lower_free_vars(head(l), s+n-1, n, menv), remove_core(tail(l), s-1, n, menv));
        }
    } else {
        return l;
    }
}

optional<context> context::remove(unsigned s, unsigned n, metavar_env const & menv) const {
    try {
        return some(context(remove_core(m_list, s, n, menv)));
    } catch (remove_no_applicable&) {
        return optional<context>();
    }
}

static list<context_entry> insert_at_core(list<context_entry> const & l, unsigned i, name const & n, expr const & d,
                                                metavar_env const & menv) {
    if (i == 0) {
        return cons(context_entry(n, d), l);
    } else {
        lean_assert(l);
        return cons(lift_free_vars(head(l), i-1, 1, menv), insert_at_core(tail(l), i-1, n, d, menv));
    }
}

context context::insert_at(unsigned i, name const & n, expr const & d, metavar_env const & menv) const {
    return context(insert_at_core(m_list, i, n, d, menv));
}
}

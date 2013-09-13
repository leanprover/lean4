/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
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
}

/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "context.h"
#include "exception.h"

namespace lean {
std::ostream & operator<<(std::ostream & out, context const & c) {
    if (c) {
        if (tail(c))
            out << tail(c) << "\n";
        context_entry const & e = head(c);
        if (e.get_name().is_anonymous())
            out << "_";
        else
            out << e.get_name();
        out << " : " << e.get_type();
    }
    return out;
}

context const & lookup(context const & c, unsigned i) {
    context const * it1 = &c;
    while (*it1) {
        if (i == 0)
            return *it1;
        --i;
        it1 = &tail(*it1);
    }
    throw exception("unknown free variable");
}
}

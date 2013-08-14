/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "context.h"
#include "exception.h"
#include "expr_formatter.h"

namespace lean {
format pp(expr_formatter & fmt, context const & c) {
    if (c) {
        format r;
        if (tail(c))
            r = format{pp(fmt, tail(c)), line()};
        context_entry const & e = head(c);
        if (e.get_name().is_anonymous())
            r += format("_");
        else
            r += format(e.get_name());
        r += format{space(), colon(), space(), fmt(e.get_type(), tail(c))};
        return r;
    } else {
        return format();
    }
}

std::ostream & operator<<(std::ostream & out, context const & c) {
    auto fmt = mk_simple_expr_formatter();
    out << pp(*fmt, c);
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

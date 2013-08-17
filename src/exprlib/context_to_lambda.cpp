/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "context_to_lambda.h"

namespace lean {
static expr g_foo = Const("foo");
expr context_to_lambda(context const & c, expr const & e) {
    if (!c) {
        return e;
    } else {
        context_entry const & entry = head(c);
        expr t;
        if (entry.get_body())
            t = g_foo(entry.get_domain(), entry.get_body());
        else
            t = g_foo(entry.get_domain());
        return context_to_lambda(tail(c), mk_lambda(entry.get_name(), t, e));
    }
}
}

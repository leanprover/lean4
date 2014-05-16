/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/exception.h"
#include "kernel/context.h"

namespace lean {
binder const & lookup(context const & c, unsigned i) {
    auto const * it = &c;
    while (*it) {
        if (i == 0)
            return head(*it);
        --i;
        it = &tail(*it);
    }
    throw exception("unknown free variable");
}
optional<binder> find(context const & c, unsigned i) {
    try {
        return optional<binder>(lookup(c, i));
    } catch (exception &) {
        return optional<binder>();
    }
}
}

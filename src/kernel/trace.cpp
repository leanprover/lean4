/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/trace.h"

namespace lean {
bool trace::has_children() const {
    buffer<trace> r;
    get_children(r);
    return !r.empty();
}
}

/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/list.h"

namespace lean {
list<unsigned> mk_list_range(unsigned from, unsigned to) {
    list<unsigned> r;
    unsigned i = to;
    while (i > from) {
        i--;
        r = cons(i, r);
    }
    return r;
}
}

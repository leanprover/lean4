/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_set.h"

namespace lean {
name mk_unique(name_set const & s, name const & suggestion) {
    name n = suggestion;
    int i  = 1;
    while (true) {
        if (!s.contains(n))
            return n;
        n = name(suggestion, i);
        i++;
    }
}
}

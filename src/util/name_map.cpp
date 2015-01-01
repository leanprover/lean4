/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/name_map.h"

namespace lean {
name const & rename_map::find(name const & k) const {
    name const * it = &k;
    while (name const * new_it = name_map<name>::find(*it)) {
        it = new_it;
    }
    return *it;
}
}

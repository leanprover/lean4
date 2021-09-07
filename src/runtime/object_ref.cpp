/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/object_ref.h"

namespace lean {
object_ref mk_cnstr(unsigned tag, unsigned num_objs, object ** objs, unsigned scalar_sz) {
    object * r = alloc_cnstr(tag, num_objs, scalar_sz);
    for (unsigned i = 0; i < num_objs; i++) {
        cnstr_set(r, i, objs[i]);
    }
    return object_ref(r);
}
}

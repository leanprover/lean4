/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "library/type_util.h"

namespace lean {
unsigned get_expect_num_args(type_checker & tc, expr e) {
    name_generator ngen = tc.mk_ngen();
    unsigned r = 0;
    while (true) {
        e = tc.whnf(e).first;
        if (!is_pi(e))
            return r;
        // TODO(Leo): try to avoid the following instantiate.
        expr local = mk_local(ngen.next(), binding_name(e), binding_domain(e), binding_info(e));
        e = instantiate(binding_body(e), local);
        r++;
    }
}
}

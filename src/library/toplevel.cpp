/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "toplevel.h"
#include "builtin.h"
#include "basic_thms.h"
#include "arith.h"

namespace lean {
void init_toplevel(environment & env) {
    add_basic_theory(env);
    add_basic_thms(env);
    add_arith_theory(env);
}
environment mk_toplevel() {
    environment r;
    init_toplevel(r);
    return r;
}
}

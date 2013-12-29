/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "library/basic_thms.h"
#include "library/arith/arith.h"
#include "library/all/all.h"

namespace lean {
void import_all(environment const & env) {
    import_kernel(env);
    import_basic_thms(env);
    import_arith(env);
}
environment mk_toplevel() {
    environment r;
    import_all(r);
    return r;
}
}

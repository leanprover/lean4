/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/builtin.h"
#include "library/basic_thms.h"
#include "library/arith/arithlibs.h"
#include "library/cast/castlib.h"
#include "library/import_all/import_all.h"

namespace lean {
void import_all(environment & env) {
    import_basiclib(env);
    import_basicthms(env);
    import_castlib(env);
    import_arithlibs(env);
}
environment mk_toplevel() {
    environment r;
    import_all(r);
    return r;
}
}

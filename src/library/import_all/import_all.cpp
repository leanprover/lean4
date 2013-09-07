/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "import_all.h"
#include "builtin.h"
#include "basic_thms.h"
#include "arithlibs.h"
#include "castlib.h"

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

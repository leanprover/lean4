/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "arithlibs.h"

namespace lean {
void import_arithlibs(environment & env) {
    import_natlib(env);
    import_intlib(env);
    import_reallib(env);
    import_int_to_real_coercions(env);
    import_specialfnlib(env);
}
}

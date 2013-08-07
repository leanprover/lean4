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
environment mk_toplevel() {
    environment r;
    add_basic_theory(r);
    add_basic_thms(r);
    add_int_theory(r);
    return r;
}
}

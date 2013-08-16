/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontend.h"
#include "builtin.h"

namespace lean {
/**
   \brief Initialize builtin notation.
*/
void init_builtin_notation(frontend & f) {
    f.add_infixl("\u2227", 13, const_name(mk_and_fn()));
    f.add_infixl("\u2228", 14, const_name(mk_or_fn()));
    f.add_prefix("\u00ac", 3, const_name(mk_not_fn()));
}
}

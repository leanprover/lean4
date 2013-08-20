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
    f.add_prefix("\u00ac", 40, mk_not_fn());
    f.add_infixr("&&", 35, mk_and_fn());
    f.add_infixr("/\\", 35, mk_and_fn());
    f.add_infixr("\u2227", 35, mk_and_fn());
    f.add_infixr("||", 30, mk_or_fn());
    f.add_infixr("\\/", 30, mk_or_fn());
    f.add_infixr("\u2228", 30, mk_or_fn());
    f.add_infixr("=>", 25, mk_implies_fn());
    f.add_infixr("\u21D2", 25, mk_implies_fn());
    f.add_infixr("<=>", 25, mk_iff_fn());
    f.add_infixr("\u21D4", 25, mk_iff_fn());
}
}

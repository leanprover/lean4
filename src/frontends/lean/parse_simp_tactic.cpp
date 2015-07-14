/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/exact_tactic.h"
#include "frontends/lean/parser.h"

namespace lean {
expr parse_simp_tactic(parser & p) {
    // TODO(Leo)
    auto pos = p.pos();
    expr sorry = p.mk_sorry(pos);
    return p.mk_app(get_exact_tac_fn(), sorry, pos);
}
}

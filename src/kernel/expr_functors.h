/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {

struct expr_hash {
    unsigned operator()(expr const & e) const { return e.hash(); }
};
struct expr_eqp {
    bool operator()(expr const & e1, expr const & e2) const { return eqp(e1, e2); }
};

struct expr_cell_hash {
    unsigned operator()(expr_cell * e) const { return e->hash(); }
};
struct expr_cell_eqp {
    bool operator()(expr_cell * e1, expr_cell * e2) const { return e1 == e2; }
};

}

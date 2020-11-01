/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "kernel/expr.h"

namespace lean {
/** \brief Replace the free variables s[0], ..., s[n-1] in e with bound variables bvar(n-1), ..., bvar(0). */
expr abstract(expr const & e, unsigned n, expr const * s);
inline expr abstract(expr const & e, expr const & s) { return abstract(e, 1, &s); }
expr abstract(expr const & e, name const & n);

}

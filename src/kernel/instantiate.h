/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/**
   \brief Replace the free variables with indices 0, ..., n-1 with s[n-1], ..., s[0] in e.

   \pre s[0], ..., s[n-1] must be closed expressions (i.e., no free variables).
*/
expr instantiate_with_closed(expr const & e, unsigned n, expr const * s);
inline expr instantiate_with_closed(expr const & e, std::initializer_list<expr> const & l) {
    return instantiate_with_closed(e, l.size(), l.begin());
}
inline expr instantiate_with_closed(expr const & e, expr const & s) { return instantiate_with_closed(e, 1, &s); }

/**
   \brief Replace the free variables with indices 0, ..., n-1 with s[n-1], ..., s[0] in e.
*/
expr instantiate(expr const & e, unsigned n, expr const * s);
inline expr instantiate(expr const & e, std::initializer_list<expr> const & l) { return instantiate(e, l.size(), l.begin()); }
inline expr instantiate(expr const & e, expr const & s) { return instantiate(e, 1, &s); }
}

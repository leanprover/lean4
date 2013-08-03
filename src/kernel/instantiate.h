/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {
/**
   \brief Replace the free variables with indices 0,...,n-1 with s[n-1],...,s[0] in e.

   \pre s[0], ..., s[n-1] must be closed expressions (i.e., no free variables).
*/
expr instantiate_with_closed(unsigned n, expr const * s, expr const & e);
inline expr instantiate_with_closed(expr const & s, expr const & e) { return instantiate_with_closed(1, &s, e); }

/**
   \brief Replace the free variables with indices 0,...,n-1 with s[n-1],...,s[0] in e.
*/
expr instantiate(unsigned n, expr const * s, expr const & e);
inline expr instantiate(expr const & s, expr const & e) { return instantiate(1, &s, e); }

}

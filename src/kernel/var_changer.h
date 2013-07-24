/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "expr.h"

namespace lean {

/**
   \brief Replace the expressions s[0], ..., s[n-1] in e with var(n-1), ..., var(0).

   Structural equality is used to compare subexpressions of e with the s[i]'s.

   \pre s[0], ..., s[n-1] must be closed expressions (i.e., no free variables).
*/
expr abstract(unsigned n, expr const * s, expr const & e);
inline expr abstract(expr const & s, expr const & e) { return abstract(1, &s, e); }

/**
   \brief Replace the expressions s[0], ..., s[n-1] in e with var(n-1), ..., var(0).

   Pointer comparison is used to compare subexpressions of e with the s[i]'s.

   \pre s[0], ..., s[n-1] must be closed expressions (i.e., no free variables).
*/
expr abstract_p(unsigned n, expr const * s, expr const & e);
inline expr abstract_p(expr const & s, expr const & e) { return abstract_p(1, &s, e); }

/**
   \brief Replace the free variables with indices 0,...,n-1 with s[n-1],...,s[0] in e.

   \pre s[0], ..., s[n-1] must be closed expressions (i.e., no free variables).
*/
expr instantiate(unsigned n, expr const * s, expr const & e);
inline expr instantiate(expr const & s, expr const & e) { return instantiate(1, &s, e); }

/**
   \brief Substitute s with t in e.

   \pre s and t must be closed expressions (i.e., no free variables)
*/
inline expr substitute(expr const & s, expr const & t, expr const & e) {
    return instantiate(t, abstract(s, e));
}

}

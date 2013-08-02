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
   \brief Create a lambda expression (lambda (x : t) b), the term b is abstracted using abstract(constant(x), b).
*/
inline expr fun(name const & n, expr const & t, expr const & b) { return lambda(n, t, abstract(constant(n), b)); }
inline expr fun(char const * n, expr const & t, expr const & b) { return fun(name(n), t, b); }
/**
   \brief Create a Pi expression (pi (x : t) b), the term b is abstracted using abstract(constant(x), b).
*/
inline expr Fun(name const & n, expr const & t, expr const & b) { return pi(n, t, abstract(constant(n), b)); }
inline expr Fun(char const * n, expr const & t, expr const & b) { return Fun(name(n), t, b); }
}

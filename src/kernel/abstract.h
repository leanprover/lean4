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
expr abstract(expr const & e, unsigned n, expr const * s);
inline expr abstract(expr const & e, expr const & s) { return abstract(e, 1, &s); }

/**
   \brief Replace the expressions s[0], ..., s[n-1] in e with var(n-1), ..., var(0).

   Pointer comparison is used to compare subexpressions of e with the s[i]'s.

   \pre s[0], ..., s[n-1] must be closed expressions (i.e., no free variables).
*/
expr abstract_p(expr const & e, unsigned n, expr const * s);
inline expr abstract_p(expr const & e, expr const & s) { return abstract_p(e, 1, &s); }

/**
   \brief Create a lambda expression (lambda (x : t) b), the term b is abstracted using abstract(b, constant(x)).
*/
inline expr fun(name const & n, expr const & t, expr const & b) { return lambda(n, t, abstract(b, constant(n))); }
inline expr fun(char const * n, expr const & t, expr const & b) { return fun(name(n), t, b); }
inline expr fun(expr const & n, expr const & t, expr const & b) { return lambda(const_name(n), t, abstract(b, n)); }
/**
   \brief Create a Pi expression (pi (x : t) b), the term b is abstracted using abstract(b, constant(x)).
*/
inline expr Fun(name const & n, expr const & t, expr const & b) { return pi(n, t, abstract(b, constant(n))); }
inline expr Fun(char const * n, expr const & t, expr const & b) { return Fun(name(n), t, b); }
inline expr Fun(expr const & n, expr const & t, expr const & b) { return pi(const_name(n), t, abstract(b, n)); }
}

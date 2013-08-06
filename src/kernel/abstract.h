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
inline expr Fun(name const & n, expr const & t, expr const & b) { return mk_lambda(n, t, abstract(b, mk_constant(n))); }
inline expr Fun(char const * n, expr const & t, expr const & b) { return Fun(name(n), t, b); }
inline expr Fun(expr const & n, expr const & t, expr const & b) { return mk_lambda(const_name(n), t, abstract(b, n)); }
inline expr Fun(std::pair<expr const &, expr const &> const & p, expr const & b) { return Fun(p.first, p.second, b); }
       expr Fun(std::initializer_list<std::pair<expr const &, expr const &>> const & l, expr const & b);

/**
   \brief Create a Pi expression (pi (x : t) b), the term b is abstracted using abstract(b, constant(x)).
*/
inline expr Pi(name const & n, expr const & t, expr const & b) { return mk_pi(n, t, abstract(b, mk_constant(n))); }
inline expr Pi(char const * n, expr const & t, expr const & b) { return Pi(name(n), t, b); }
inline expr Pi(expr const & n, expr const & t, expr const & b) { return mk_pi(const_name(n), t, abstract(b, n)); }
inline expr Pi(std::pair<expr const &, expr const &> const & p, expr const & b) { return Pi(p.first, p.second, b); }
       expr Pi(std::initializer_list<std::pair<expr const &, expr const &>> const & l, expr const & b);
}

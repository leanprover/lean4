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

/* ------ LEGACY CODE -------------
   The following API is to support legacy
   code where the type of a local constant (aka free variable)
   was stored in the local constant itself.
   This approach was used in Lean2, and is being abandoned in Lean4.

   TODO(Leo): delete */

/** \brief Create a lambda-expression by abstracting the given local constants over b */
expr Fun(unsigned num, expr const * locals, expr const & b);
inline expr Fun(expr const & local, expr const & b) { return Fun(1, &local, b); }
inline expr Fun(std::initializer_list<expr> const & locals, expr const & b) { return Fun(locals.size(), locals.begin(), b); }
template<typename T> expr Fun(T const & locals, expr const & b) { return Fun(locals.size(), locals.data(), b); }

/** \brief Create a Pi-expression by abstracting the given local constants over b */
expr Pi(unsigned num, expr const * locals, expr const & b);
inline expr Pi(expr const & local, expr const & b) { return Pi(1, &local, b); }
inline expr Pi(std::initializer_list<expr> const & locals, expr const & b) { return Pi(locals.size(), locals.begin(), b); }
template<typename T> expr Pi(T const & locals, expr const & b) { return Pi(locals.size(), locals.data(), b); }

}

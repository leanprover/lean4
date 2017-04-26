/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "kernel/expr.h"

namespace lean {
/**
   \brief Replace the expressions s[0], ..., s[n-1] in e with var(n-1), ..., var(0).

   Structural equality is used to compare subexpressions of e with the s[i]'s.

   \pre s[0], ..., s[n-1] must be closed expressions (i.e., no free variables).
*/
expr abstract(expr const & e, unsigned n, expr const * s);
inline expr abstract(expr const & e, expr const & s) { return abstract(e, 1, &s); }
inline expr abstract(expr const & e, std::initializer_list<expr> const & l) { return abstract(e, l.size(), l.begin()); }
/** \brief Replace s with variable #i in the given expression. \pre s is closed */
expr abstract(expr const & e, expr const & s, unsigned i);

/** \brief Similar to abstract, but all values in s are local constants. */
expr abstract_locals(expr const & e, unsigned n, expr const * s);
inline expr abstract_local(expr const & e, expr const & s) { return abstract_locals(e, 1, &s); }
expr abstract_local(expr const & e, name const & l);

/** \brief Create a lambda-expression by abstracting the given local constants over b */
expr Fun(unsigned num, expr const * locals, expr const & b, bool use_cache = true);
inline expr Fun(expr const & local, expr const & b, bool use_cache = true) { return Fun(1, &local, b, use_cache); }
inline expr Fun(std::initializer_list<expr> const & locals, expr const & b, bool use_cache = true) { return Fun(locals.size(), locals.begin(), b, use_cache); }
template<typename T> expr Fun(T const & locals, expr const & b, bool use_cache = true) { return Fun(locals.size(), locals.data(), b, use_cache); }

/** \brief Create a Pi-expression by abstracting the given local constants over b */
expr Pi(unsigned num, expr const * locals, expr const & b, bool use_cache = true);
inline expr Pi(expr const & local, expr const & b, bool use_cache = true) { return Pi(1, &local, b, use_cache); }
inline expr Pi(std::initializer_list<expr> const & locals, expr const & b, bool use_cache = true) { return Pi(locals.size(), locals.begin(), b, use_cache); }
template<typename T> expr Pi(T const & locals, expr const & b, bool use_cache = true) { return Pi(locals.size(), locals.data(), b, use_cache); }

/** \brief Clear thread local caches used by Pi/Fun procedures
    We clear the caches whenever we enable expression caching (aka max sharing).
    We do that because the cache may still contain expressions that are not maximally shared. */
void clear_abstract_cache();
}

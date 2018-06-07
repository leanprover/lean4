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
expr abstract(expr const & e, name const & l);

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

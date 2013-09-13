/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/context.h"

namespace lean {
/** \brief Return true iff \c n occurs in \c m */
bool occurs(expr const & n, expr const & m);
/** \brief Return true iff there is a constant named \c n in \c m. */
bool occurs(name const & n, expr const & m);
/** \brief Return true iff \c n ocurs in context \c c. */
bool occurs(expr const & n, context const & c);
/** \brief Return true iff there is a constant named \c n in context \c c. */
bool occurs(name const & n, context const & c);
/** \brief Return true iff \c n ocurs in context \c c or the array of expressions es[sz]. */
bool occurs(expr const & n, context const & c, unsigned sz, expr const * es);
inline bool occurs(expr const & n, context const & c, std::initializer_list<expr> const & l) { return occurs(n, c, l.size(), l.begin()); }
/** \brief Return true iff there is a constant named \c n in context \c c or the array of expressions es[sz]. */
bool occurs(name const & n, context const & c, unsigned sz, expr const * es);
inline bool occurs(name const & n, context const & c, std::initializer_list<expr> const & l) { return occurs(n, c, l.size(), l.begin()); }
}

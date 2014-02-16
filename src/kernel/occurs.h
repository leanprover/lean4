/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
/** \brief Return true iff \c n occurs in \c m */
bool occurs(expr const & n, expr const & m);
/** \brief Return true iff there is a constant named \c n in \c m. */
bool occurs(name const & n, expr const & m);
}

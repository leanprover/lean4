/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
/** \brief Total order on expressions */
bool is_lt(expr const & a, expr const & b);
inline bool operator<(expr const & a, expr const & b)  { return is_lt(a, b); }
inline bool operator>(expr const & a, expr const & b)  { return is_lt(b, a); }
inline bool operator<=(expr const & a, expr const & b) { return !is_lt(b, a); }
inline bool operator>=(expr const & a, expr const & b) { return !is_lt(a, b); }
}

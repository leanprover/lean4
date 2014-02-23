/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
namespace lean {
/**
    \brief Total order on expressions.

    \remark If \c use_hash is true, then we use the hash_code to
    partially order expressions. Setting use_hash to false is useful
    for testing the code.
*/
bool is_lt(expr const & a, expr const & b, bool use_hash);
inline bool operator<(expr const & a, expr const & b)  { return is_lt(a, b, true); }
inline bool operator>(expr const & a, expr const & b)  { return is_lt(b, a, true); }
inline bool operator<=(expr const & a, expr const & b) { return !is_lt(b, a, true); }
inline bool operator>=(expr const & a, expr const & b) { return !is_lt(a, b, true); }

bool is_lt(level const & a, level const & b, bool use_hash);
bool is_lt(levels const & as, levels const & bs, bool use_hash);
}

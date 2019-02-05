/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include "runtime/hash.h"
#include "library/expr_lt.h"

namespace lean {
inline bool is_lt(expr_pair const & p1, expr_pair const & p2, bool use_hash) {
    return is_lt(p1.first, p2.first, use_hash) || (p1.first == p2.first && is_lt(p1.second, p2.second, use_hash));
}
struct expr_pair_quick_cmp {
    int operator()(expr_pair const & p1, expr_pair const & p2) const { return is_lt(p1, p2, true) ? -1 : (p1 == p2 ? 0 : 1);  }
};
}

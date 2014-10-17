/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_set>
#include <utility>
#include <functional>
#include "util/hash.h"
#include "kernel/expr.h"

namespace lean {
// =======================================
// Expression Set
// Remark: to expressions are assumed to be equal if they are "pointer-equal"
typedef std::unordered_set<expr, expr_hash_alloc, expr_eqp> expr_set;
// =======================================

// Similar to expr_set, but using structural equality
typedef std::unordered_set<expr, expr_hash, std::equal_to<expr>> expr_struct_set;
}
